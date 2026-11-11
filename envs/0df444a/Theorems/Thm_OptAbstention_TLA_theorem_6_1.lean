-- Prove2me | Theorems.Thm_OptAbstention_TLA_theorem_6_1
-- name    : OptAbstention.TLA.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:09:27.936337+00:00
-- url     : https://prove2.me/theorems/3d9f9f06-0a07-4c14-8a96-c1a39057f075
-- title:
--   Theorem 6.1: L1 sandwiching gives a $(\lambda+\mathrm{opt}_{\mathrm{train}}+\varepsilon,\eta,\delta)$-TLA learner with $\mathrm{poly}(Z)\log(1/\delta)$ samples and time (as printed; insight I1)
-- statement:
--   Let $B\ge1$, $\varepsilon,\eta,\delta\in(0,1)$, $X\subseteq\mathbb R^d$, $D$ a distribution on $X$, $\mathcal C\subseteq\{\pm1\}^X$ a concept class and $\ell=L_1(\varepsilon/2,B,\mathcal C,D)$. Write $Z=M_{D,\ell}B(d+1)^\ell/(\varepsilon\eta)$. Then there is a
--   $$(\lambda+\mathrm{opt}_{\mathrm{train}}+\varepsilon,\ \eta,\ \delta)\text{-TLA algorithm for }\mathcal C\text{ w.r.t. }D$$
--   with $\mathrm{poly}(Z)\log(1/\delta)$ sample complexity and $\mathrm{poly}(|S_{\mathrm{test}}|,Z)\log(1/\delta)$ runtime. Here $\lambda=\lambda(\bar D_{\mathrm{train}},U(\bar S_{\mathrm{test}});\mathcal C)$ is the joint error of the class on the training distribution and the labeled test set, and $\mathrm{opt}_{\mathrm{train}}$ the best training error.
--
--   Precisely: there are universal $C,k$ such that for every instance with $M_{D,\ell}<\infty$ there is a program that on every run on a test list of length $n\ge1$ draws at most $C Z^k\log(1/\delta)$ labeled examples and halts within $C(nZ)^k\log(1/\delta)$ steps, and that is a $(\lambda+\mathrm{opt}_{\mathrm{train}}+\varepsilon,\eta,\delta)$-TLA learner: its selective error is at most $\lambda+\mathrm{opt}_{\mathrm{train}}+\varepsilon$ for every labeling of every test list, and its abstention rate is at most $d_{\mathrm{TV}}(U(S_{\mathrm{test}}),U(S_{\mathrm{cln}}))+\eta$ against every adversary, each with failure probability at most $\delta$.
--
--   This is the main theorem of the paper: the abstention rate matches the information-theoretic benchmark $d_{\mathrm{TV}}+\eta$ while the selective error stays at $\lambda+\mathrm{opt}_{\mathrm{train}}+\varepsilon$.
--
--   **Formalization Note.** The program is chosen after $(d,X,D,\mathcal C,B,\varepsilon,\eta,\delta)$ but before $\bar D_{\mathrm{train}}$, the test list, its labels and the adversary, and sees only $n$, the test points, the example stream and its tape.
--
--   Differences from the source:
--   - encoding: an algorithm with sample complexity and runtime → a program of the randomized sampling real RAM; on every run on a test list of length n ≥ 1 (example stream in X), samples ≤ C·Z^k·log(1/δ) and charged steps ≤ C·(nZ)^k·log(1/δ), C and k universal and fixed first; reason: the paper names no model; worst-case bounds on every run; poly(n, Z) as C(nZ)^k is an equivalent family since n, Z ≥ 1
--   - encoding: ℓ := L1(ε/2, B, C, D) → hypothesis IsL1Degree D (ε/2) B C ℓ (a sandwiching degree exists and ℓ is the least); reason: the minimum is defined only when some degree works
--   - encoding: poly(M_{D,ℓ}B(d+1)^ℓ/(εη)) → hypothesis M_{D,ℓ} < ∞, and M_{D,ℓ} used as a real; reason: the bounds are meaningless for M_{D,ℓ} = ∞; this excludes only that undefined case
--   - reading: concepts in {±1}^X → measurable functions with values ±1 as reals; reason: Pr_{D̄}[f(x) ≠ y] is defined only for measurable f
--   - encoding: λ and opt_train → infima in [0,∞] (⊤ for an empty class); reason: no junk value 0 for an empty class
--   - reading: 'sufficiently large' S_cln; an adversary that replaces elements of S_cln → one threshold N independent of D̄_train, n and the adversary; the adversary is any Markov kernel on lists of length n, independent of the example stream and the tape; reason: the uniform threshold is the stronger reading; a kernel is the most general randomized replacement of the same number of points
--   - encoding: finite multisets → lists Fin n → X, compared through their occurrences; reason: footnote 2: occurrences are distinct elements; same instances
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
--   - generalization: X ⊆ ℝ^d with d ∈ ℕ* (§5 notation) → every d ∈ ℕ, including d = 0; reason: the source's dimensions are among them
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 13, Theorem 6.1 (proved pp. 18–19)

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_Learner

open MeasureTheory

namespace OptAbstention.TLA

/-- Theorem 6.1, p. 13, as printed with log(1/δ): universal constants first, then for each
problem a program with poly(M B (d+1)^ℓ/(εη)) log(1/δ) samples and poly(n, …) log(1/δ) steps on
every run that is a (λ + opt_train + ε, η, δ)-TLA learner. -/
theorem theorem_6_1 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (B ε η δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → 1 ≤ B → 0 < ε → ε < 1 → 0 < η → η < 1 →
      0 < δ → δ < 1 → IsL1Degree D (ε / 2) B Cl ℓ → momentBound D ℓ ≠ ⊤ →
      ∃ P : Program, Admissible P ∧
        (∀ (n : ℕ), 1 ≤ n → ∀ (xs : Fin n → X) (ξ : ExStream d), (∀ i, (ξ i).1 ∈ X) →
          ∀ ν : Tape,
          HaltsWithin P d ξ ν (testInit xs)
            (C * ((n : ℝ) * ((momentBound D ℓ).toReal * B * ((d : ℝ) + 1) ^ ℓ / (ε * η))) ^ k *
              Real.log (1 / δ))
            (C * ((momentBound D ℓ).toReal * B * ((d : ℝ) + 1) ^ ℓ / (ε * η)) ^ k *
              Real.log (1 / δ))) ∧
        IsTLALearner P D
          (fun Dbar _ xs ys => jointErr Dbar Cl xs ys + optTrain Dbar Cl + ENNReal.ofReal ε)
          η δ := by sorry

end OptAbstention.TLA
