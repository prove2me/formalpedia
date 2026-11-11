-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_F_2
-- name    : OptAbstention.TLA.lemma_F_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:09:01.206705+00:00
-- url     : https://prove2.me/theorems/1f00385f-3ada-4e38-8e58-8a3cb3963c0b
-- title:
--   Lemma F.2: grid search with Bernoulli rounding has selective error $\le\Pr_D[h\ne f]+5\varepsilon/8$ and abstention $\le d_{\mathrm{TV}}+\eta$ in time $O(1/\eta)\mathrm{poly}$
-- statement:
--   Let $X\subseteq\mathbb R^d$, $B\ge1$, $\varepsilon,\eta,\delta\in(0,1)$, $h:X\to\{\pm1\}$, $D$ a distribution on $X$, $\mathcal C$ a class and $\ell=L_1(\varepsilon/2,B,\mathcal C,D)$. There is a randomized algorithm that takes $h,S,S',\ell,B,\varepsilon,\eta$ as input ($S'$ nonempty), runs in time $O(1/\eta)\,\mathrm{poly}((d+1)^\ell,|S|,|S'|)$ and outputs $g\in\{0,1\}^{S'}$ such that, with $S$ i.i.d. from $D$:
--
--   1. if $|S|\gtrsim M_{D,\ell}B^2(d+1)^{4\ell}/(\varepsilon\delta)^2$ and $|S'|\gtrsim\log(2/\delta)/\varepsilon^2$, then for every $f\in\mathcal C$, with probability at least $1-\delta$ over $S$ and the algorithm's randomness, $\Pr_{x\sim U(S')}[h(x)\ne f(x)\wedge g_x=1]\le\Pr_{x\sim D}[h(x)\ne f(x)]+5\varepsilon/8$;
--   2. if $S_{\mathrm{cln}}$ is i.i.d. from $D$ with $|S|\gtrsim M_{D,\ell}B^2(d+1)^{4\ell}/(\varepsilon\delta)^2$ and $|S_{\mathrm{cln}}|\gtrsim M_{D,\ell}B^2(d+1)^{4\ell}/(\varepsilon\delta)^2+\log(2/\delta)/\eta^2$, then with probability at least $1-\delta/2$ over $(S,S_{\mathrm{cln}})$, for every $S'$ with $|S'|=|S_{\mathrm{cln}}|$, with probability at least $1-\delta/2$ over the algorithm's randomness,
--   $$\Pr_{x\sim U(S')}[g_x=0]\le d_{\mathrm{TV}}(U(S'),U(S_{\mathrm{cln}}))+\eta .$$
--
--   **Formalization Note.** One program per dimension $d$, quantified before $X,D,\mathcal C,h,B,\varepsilon,\eta,\delta$; its $\delta$ input cell holds $0$. $O(1/\eta)\mathrm{poly}(a,b,c)$ is $(C/\eta)(a+b+c)^k$ and $\gtrsim$ is $\ge C\cdot$, with universal $C,k$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm and its running time (no model named) → a program of the randomized sampling real RAM (rational literals, uniform tape, no sqrt/exp/log/floor/LP instruction); running time = charged steps, bounded on every input and every tape; reason: the paper names no model; every extra primitive would weaken the existence claim
--   - encoding: the algorithm takes h as input → h is given by its values at the points of S and S′; reason: a machine cannot receive a function; this restricts the algorithm, so the statement is no weaker
--   - reading: 'there is a randomized algorithm that takes h, S, S′, ℓ, B, ε, η as input' after X, B, ε, η, δ, h, D, C are fixed → one program per d, chosen before X, D, C, h, B, ε, η, δ, with δ not given to it; reason: the algorithm receives these values as inputs; the reading where the program may depend on them is the weaker one
--   - encoding: O(1/η)poly((d+1)^ℓ, |S|, |S′|); |·| ≳ E → (C/η)·((d+1)^ℓ + |S| + |S′|)^k; |·| ≥ C·E, C and k universal; reason: equivalent families of bounds for arguments ≥ 1
--   - reading: h: X → {±1} and C ⊆ {±1}^X → h and every f ∈ C measurable, values ±1 as reals; reason: Pr_D[h(x) ≠ f(x)] and E_D[h(x)x^α] are defined only for measurable functions
--   - encoding: finite multisets → lists Fin n → X, compared through their occurrences; reason: footnote 2: occurrences are distinct elements; same instances
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 49, Lemma F.2

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_SelectorIO

open MeasureTheory

namespace OptAbstention.TLA

open Classical in
/-- Lemma F.2, p. 49: one randomized program (per dimension `d`) that takes `h` (by its values at
the points), `S`, `S′`, `ℓ`, `B`, `ε`, `η` and runs in time `(C/η)·((d+1)^ℓ + |S| + |S′|)^k` on
every input and every tape, with the selective-error guarantee (item 1) and the abstention
guarantee against every `S′` of size `|S_cln|` (item 2). `≳` is `≥ C·`. The algorithm does not
receive `δ`: the `δ` cell of its input is `0`. -/
theorem lemma_F_2 : ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ d : ℕ, ∃ P : Program,
    Admissible P ∧ NoSample P ∧
    ∀ (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (h : X → ℝ) (B ε η δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → IsConcept X h → 1 ≤ B →
      0 < ε → ε < 1 → 0 < η → η < 1 → 0 < δ → δ < 1 → IsL1Degree D (ε / 2) B Cl ℓ →
      -- running time, on every input with `S′` nonempty and every tape
      (∀ (m n' : ℕ), 1 ≤ n' → ∀ (S : Fin m → X) (S' : Fin n' → X) (ν : Tape),
        HaltsWithin P d (noExamples d) ν
          (selectorInit ℓ B ε η 0 (fun i => (S i : Pt d)) (fun i => h (S i))
            (fun j => (S' j : Pt d)) (fun j => h (S' j)))
          (C / η * (((d : ℝ) + 1) ^ ℓ + m + n') ^ k) 0) ∧
      -- item 1: selective error
      (∀ (m n' : ℕ), 1 ≤ n' →
        ENNReal.ofReal C * momentBound D ℓ *
            ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (4 * ℓ) / (ε * δ) ^ 2) ≤ (m : ENNReal) →
        C * Real.log (2 / δ) / ε ^ 2 ≤ (n' : ℝ) →
        ∀ (S' : Fin n' → X), ∀ f ∈ Cl,
          ((Measure.pi fun _ : Fin m => D).prod tapeLaw)
            {q | ¬ ∃ St, finalState P d (noExamples d) q.2
                (selectorInit ℓ B ε η 0 (fun i => (q.1 i : Pt d)) (fun i => h (q.1 i))
                  (fun j => (S' j : Pt d)) (fun j => h (S' j))) = some St ∧
              ValidSelector St n' ∧
              frac (fun j : Fin n' => h (S' j) ≠ f (S' j) ∧ outSel St j = 1) ≤
                (D {x | h x ≠ f x}).toReal + 5 * ε / 8}
            ≤ ENNReal.ofReal δ) ∧
      -- item 2: abstention rate
      (∀ (m n : ℕ),
        ENNReal.ofReal C * momentBound D ℓ *
            ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (4 * ℓ) / (ε * δ) ^ 2) ≤ (m : ENNReal) →
        ENNReal.ofReal C * momentBound D ℓ *
            ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (4 * ℓ) / (ε * δ) ^ 2) +
          ENNReal.ofReal (C * Real.log (2 / δ) / η ^ 2) ≤ (n : ENNReal) →
        ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin n => D))
          {q | ¬ ∀ S' : Fin n → X,
            tapeLaw {ν | ¬ ∃ St, finalState P d (noExamples d) ν
                (selectorInit ℓ B ε η 0 (fun i => (q.1 i : Pt d)) (fun i => h (q.1 i))
                  (fun j => (S' j : Pt d)) (fun j => h (S' j))) = some St ∧
              ValidSelector St n ∧
              frac (fun j : Fin n => outSel St j = 0) ≤ empTV S' q.2 + η}
              ≤ ENNReal.ofReal (δ / 2)}
          ≤ ENNReal.ofReal (δ / 2)) := by sorry

end OptAbstention.TLA
