-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_F_3
-- name    : OptAbstention.TLA.lemma_F_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:09:02.121285+00:00
-- url     : https://prove2.me/theorems/b4c08610-c93a-4fa2-ad72-58c4231ac500
-- title:
--   Lemma F.3 (= Lemma 6.8): the blocked grid search has selective error $\le\Pr_D[h\ne f]+3\varepsilon/4$ and abstention $\le d_{\mathrm{TV}}+\eta$ against every randomized adversary
-- statement:
--   Let $X\subseteq\mathbb R^d$, $B\ge1$, $\varepsilon,\eta,\delta\in(0,1)$, $h:X\to\{\pm1\}$, $D$ a distribution on $X$, $\mathcal C$ a class and $\ell=L_1(\varepsilon/2,B,\mathcal C,D)$. Let $S$ be i.i.d. from $D$ with $|S|\gtrsim M_{D,\ell}B^2(d+1)^{4\ell}\log(2/\eta)\log(2/\delta)/(\varepsilon^5\eta^3)$ and $S'$ nonempty. There is a randomized algorithm taking $h,S,S',\ell,B,\varepsilon,\eta,\delta$, running in time $\mathrm{poly}((d+1)^\ell,|S|,|S'|,1/\varepsilon,1/\eta)\log(2/\delta)$ and outputting $g:S'\to\{0,1\}$ such that:
--
--   1. for every $f\in\mathcal C$, with probability at least $1-\delta$ over $S$ and the algorithm, $\Pr_{x\sim U(S')}[h(x)\ne f(x)\wedge g(x)=1]\le\Pr_{x\sim D}[h(x)\ne f(x)]+3\varepsilon/4$;
--   2. for every (possibly randomized) adversary mapping a multiset to one of the same cardinality, with $S_{\mathrm{cln}}$ i.i.d. from $D$ independent of $S$, $S'=\mathrm{adv}(S_{\mathrm{cln}})$ and $|S_{\mathrm{cln}}|$ at least the same bound, with probability at least $1-\delta$,
--   $$\Pr_{x\sim U(S')}[g(x)=0]\le d_{\mathrm{TV}}(U(S'),U(S_{\mathrm{cln}}))+\eta .$$
--
--   **Formalization Note.** One program per dimension $d$; the adversary is a Markov kernel on lists of length $|S_{\mathrm{cln}}|$; poly is $C(\cdot+\dots+\cdot)^k$ with universal $C,k$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm and its running time (no model named) → a program of the randomized sampling real RAM (rational literals, uniform tape, no sqrt/exp/log/floor/LP instruction); running time = charged steps, bounded on every input and every tape; reason: the paper names no model; every extra primitive would weaken the existence claim
--   - encoding: the algorithm takes h as input → h is given by its values at the points of S and S′; reason: a machine cannot receive a function; this restricts the algorithm, so the statement is no weaker
--   - reading: 'there is a randomized algorithm that takes h, S, S′, ℓ, B, ε, η, δ as input' after the instance is fixed → one program per d, chosen before X, D, C, h, B, ε, η, δ; reason: the algorithm receives these values as inputs; the reading where the program may depend on them is the weaker one
--   - encoding: poly((d+1)^ℓ, |S|, |S′|, 1/ε, 1/η) log(2/δ); |·| ≳ E → C·((d+1)^ℓ + |S| + |S′| + 1/ε + 1/η)^k·log(2/δ); |·| ≥ C·E, C and k universal; reason: equivalent families of bounds for arguments ≥ 1
--   - generalization: an adversary mapping each multiset to a multiset of the same cardinality → any Markov kernel on lists of length n (it may also use the order of S_cln); reason: a multiset adversary is such a kernel
--   - reading: h: X → {±1} and C ⊆ {±1}^X → h and every f ∈ C measurable, values ±1 as reals; reason: Pr_D[h(x) ≠ f(x)] and E_D[h(x)x^α] are defined only for measurable functions
--   - encoding: finite multisets → lists Fin n → X, compared through their occurrences; reason: footnote 2: occurrences are distinct elements; same instances
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 51, Lemma F.3 (stated in the main text as Lemma 6.8, p. 17)

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_SelectorIO

open MeasureTheory ProbabilityTheory

namespace OptAbstention.TLA

open Classical in
/-- Lemma F.3 (= Lemma 6.8), p. 51: one randomized program (per dimension `d`) that takes `h` (by
its values at the points), `S`, `S′`, `ℓ`, `B`, `ε`, `η`, `δ`; for
`|S| ≥ C·M_{D,ℓ}B²(d+1)^{4ℓ} log(2/η) log(2/δ)/(ε⁵η³)` it runs in time
`C·((d+1)^ℓ + |S| + |S′| + 1/ε + 1/η)^k · log(2/δ)` on every tape, has selective error at most
`Pr_D[h ≠ f] + 3ε/4` (item 1) and, against every randomized same-size adversary `κ` applied to
`S_cln ∼ D^n` independent of `S`, abstention at most `d_TV(U(S′), U(S_cln)) + η` (item 2). -/
theorem lemma_F_3 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ d : ℕ, ∃ P : Program,
    Admissible P ∧ NoSample P ∧
    ∀ (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (h : X → ℝ) (B ε η δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → IsConcept X h → 1 ≤ B →
      0 < ε → ε < 1 → 0 < η → η < 1 → 0 < δ → δ < 1 → IsL1Degree D (ε / 2) B Cl ℓ →
      ∀ m : ℕ,
      ENNReal.ofReal C * momentBound D ℓ *
          ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (4 * ℓ) * Real.log (2 / η) *
            Real.log (2 / δ) / (ε ^ 5 * η ^ 3)) ≤ (m : ENNReal) →
      -- running time
      (∀ (n' : ℕ), 1 ≤ n' → ∀ (S : Fin m → X) (S' : Fin n' → X) (ν : Tape),
        HaltsWithin P d (noExamples d) ν
          (selectorInit ℓ B ε η δ (fun i => (S i : Pt d)) (fun i => h (S i))
            (fun j => (S' j : Pt d)) (fun j => h (S' j)))
          (C * (((d : ℝ) + 1) ^ ℓ + m + n' + 1 / ε + 1 / η) ^ k * Real.log (2 / δ)) 0) ∧
      -- item 1: selective error
      (∀ (n' : ℕ), 1 ≤ n' → ∀ (S' : Fin n' → X), ∀ f ∈ Cl,
          ((Measure.pi fun _ : Fin m => D).prod tapeLaw)
            {q | ¬ ∃ St, finalState P d (noExamples d) q.2
                (selectorInit ℓ B ε η δ (fun i => (q.1 i : Pt d)) (fun i => h (q.1 i))
                  (fun j => (S' j : Pt d)) (fun j => h (S' j))) = some St ∧
              ValidSelector St n' ∧
              frac (fun j : Fin n' => h (S' j) ≠ f (S' j) ∧ outSel St j = 1) ≤
                (D {x | h x ≠ f x}).toReal + 3 * ε / 4}
            ≤ ENNReal.ofReal δ) ∧
      -- item 2: abstention rate against a randomized adversary
      (∀ (n : ℕ) (κ : Kernel (Fin n → X) (Fin n → X)) [IsMarkovKernel κ],
        ENNReal.ofReal C * momentBound D ℓ *
            ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (4 * ℓ) * Real.log (2 / η) *
              Real.log (2 / δ) / (ε ^ 5 * η ^ 3)) ≤ (n : ENNReal) →
        (((Measure.pi fun _ : Fin m => D).prod
            ((Measure.pi fun _ : Fin n => D) ⊗ₘ κ)).prod tapeLaw)
          {q | ¬ ∃ St, finalState P d (noExamples d) q.2
              (selectorInit ℓ B ε η δ (fun i => (q.1.1 i : Pt d)) (fun i => h (q.1.1 i))
                (fun j => (q.1.2.2 j : Pt d)) (fun j => h (q.1.2.2 j))) = some St ∧
            ValidSelector St n ∧
            frac (fun j : Fin n => outSel St j = 0) ≤ empTV q.1.2.2 q.1.2.1 + η}
          ≤ ENNReal.ofReal δ) := by sorry

end OptAbstention.TLA
