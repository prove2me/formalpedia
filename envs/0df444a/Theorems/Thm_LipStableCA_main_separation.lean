-- Prove2me | Theorems.Thm_LipStableCA_main_separation
-- name    : LipStableCA.main_separation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:33.412205+00:00
-- url     : https://prove2.me/theorems/54cd929b-4ddf-4e45-8ccb-2872766c366b
-- title:
--   Sharp separation: TIE attains $1-\epsilon$ at Lipschitz constant $\Theta(m^2/\epsilon)$, while UT with finite Lipschitz constant attains only $\Theta(1/r)$
-- statement:
--   Let $m$ items be allocated to $n$ bidders with normalized monotone valuations. Profile distance is $d(v,w)=\sum_i\max_{B\ne\emptyset}\mathrm{ld}(v_i(B),w_i(B))$, with $\mathrm{ld}$ the logarithmic distance, and allocation laws are compared by the earth mover distance with cost $\|X(S)-X(T)\|_1$. A rule is $K$-Lipschitz if $\mathrm{EMD}(P_v,P_w)\le K\,d(v,w)$ whenever $d(v,w)<\infty$. Let $r=\min\{n,\,m/\log(m+1)\}$. The following four statements hold, with absolute constants:
--
--   1. **Truthfulness in expectation, upper bound (Theorem 4.11).** There is $C>0$ such that for all $n,m\ge 1$ and $0<\epsilon<1$ there is a mechanism that is truthful in expectation, ex-post individually rational and $(1-\epsilon)$-approximate, with Lipschitz constant at most $Cm^2/\epsilon$.
--   2. **Matching lower bound (Theorem 4.12 and the opening of §4).** There is $c>0$ such that for all $n\ge 2$, $m\ge 32$ and $0<\epsilon\le 1/16$, every $(1-\epsilon)$-approximate allocation rule, truthful or not, that is $K$-Lipschitz has $K\ge cm^2/\epsilon$.
--   3. **Universal truthfulness, impossibility (Theorem 5.1).** There is $C>0$ such that for all $n,m\ge 1$, every universally truthful mechanism with a finite Lipschitz constant that is $\alpha$-approximate has $\alpha\le C/r$. There is no bound on the Lipschitz constant.
--   4. **Universal truthfulness, tightness (Theorem 5.2).** There are $c,C>0$ such that for all $n,m\ge 1$ there is a universally truthful and ex-post individually rational mechanism that is $(c/r)$-approximate with Lipschitz constant at most $Cm$.
--
--   Together these are the paper's main result, a sharp separation between the two standard notions of truthfulness for randomized mechanisms.
--
--   **Formalization Note.** Mechanisms are measurable families over a probability space of seeds, with no restriction on the space in clause 3. Clause 3 assumes nothing about the payments. Clause 2 is stated on allocation laws, so it covers every mechanism.
--
--   Differences from the source:
--   - reading: the abstract's "sharp separation", which no single numbered theorem states → the conjunction of Theorems 4.11, 4.12, 5.1, 5.2; reason: the abstract spells "sharp" out as "optimal up to a constant factor" and $\Theta(\cdot)$; each clause is a numbered result (paper.md decision 1)
--   - generalization: Theorem 4.12 states two bidders → every $n\ge 2$; reason: the opening of §4 (p.14) claims it, and padding with zero bidders proves it; it specializes to $n=2$
--   - reading: the abstract writes $\Theta(\max\{1/n,\log m/m\})$ → $r=\min\{n,m/\log(m+1)\}$, as in Theorems 5.1, 5.2; reason: the theorems' form is the precise one and is defined at $m=1$
--   - reading: "although VCG is universally truthful and optimal" in the abstract → not a clause; reason: classical context with no numbered theorem; it enters no proof
--   - reading: a randomized mechanism "first draws a random seed" with no σ-algebra named → measurable rule over a probability space (a hypothesis in clause 3, a conclusion in clauses 1, 4); universal truthfulness as `∀ᵐ`; reason: paper.md decisions 3, 5
--   - encoding: $\mathrm{Lip}(S)\le K$, $\mathrm{Lip}(S)<\infty$ → `IsLipschitz P K`, `∃ K, IsLipschitz P K`; reason: paper.md decision 4
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypotheses `1 ≤ n` and `1 ≤ m` (clauses 1, 3, 4); reason: the paper's standing setting; excludes only the empty item set and the empty set of bidders
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), abstract, p.1 ("our main result is a sharp separation"); Theorems 4.11, 4.12, p.17; opening of §4, p.14; Theorems 5.1, 5.2, p.21

import Definitions.Def_LipStableCA_Mechanism
import Definitions.Def_LipStableCA_IsLipschitz
import Definitions.Def_LipStableCA_hardProfile
universe u
open MeasureTheory

namespace LipStableCA

/-- **Abstract, with Theorems 4.11, 4.12, 5.1, 5.2.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.1. **Formalization Note.** the conjunction of Theorems 4.11, 4.12, 5.1, 5.2: the abstract spells "sharp" out as "optimal up to a constant factor" and `Theta(·)`; each clause is a numbered result (paper.md decision 1). every `nge 2`: the opening of §4 (p.14) claims it, and padding with zero bidders proves it; it specializes to `n=2`. `r=min{n,m/log(m+1)}`, as in Theorems 5.1, 5.2: the theorems' form is the precise one and is defined at `m=1`. not a clause: classical context with no numbered theorem; it enters no proof. measurable rule over a probability space (a hypothesis in clause 3, a conclusion in clauses 1, 4); universal truthfulness as `∀ᵐ`: paper.md decisions 3, 5. `IsLipschitz P K`, `∃ K, IsLipschitz P K`: paper.md decision 4. the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. -/
theorem main_separation :
    (∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (M : Mechanism n m Ω),
        M.Measurable ∧ M.PayMeasurable ∧ M.IsTIE μ ∧ M.IsExPostIR μ ∧
          IsApprox (M.law μ) (1 - ϵ) ∧ IsLipschitz (M.law μ) (C * (m : ℝ) ^ 2 / ϵ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 2 ≤ n → 32 ≤ m → ∀ ϵ : ℝ, 0 < ϵ → ϵ ≤ 1 / 16 →
      ∀ P : Profile n m → Alloc n m → ℝ, (∀ v, IsProfile v → IsLaw (P v)) → IsApprox P (1 - ϵ) →
        ∀ K : ℝ, IsLipschitz P K → c * (m : ℝ) ^ 2 / ϵ ≤ K) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (M : Mechanism n m Ω), M.Measurable → M.IsUT μ → (∃ K, IsLipschitz (M.law μ) K) →
          ∀ α : ℝ, IsApprox (M.law μ) α → α ≤ C / ratioParam n m) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (M : Mechanism n m Ω),
        M.Measurable ∧ M.PayMeasurable ∧ M.IsUT μ ∧ M.IsExPostIR μ ∧
          IsApprox (M.law μ) (c / ratioParam n m) ∧ IsLipschitz (M.law μ) (C * (m : ℝ))) := by sorry

end LipStableCA
