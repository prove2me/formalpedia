-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_45
-- name    : MultiCorrectPAC.Demo.theorem_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:51.890181+00:00
-- url     : https://prove2.me/theorems/f9885568-c93f-457e-9651-eca8c9c324fa
-- title:
--   Theorem 45 (Theorem D) — countable labels: realizable ⇔ agnostic full-set learnability ⇔ d∩_pack,γ < ∞, with rates (62)–(63); d∩_DS is not the right dimension for ℓ ≥ 2
-- statement:
--   Fix $\ell\ge1$ and $0<\gamma<1/(\ell+1)$. There is $c>0$ depending only on $\ell$ and $\gamma$ such that for countable $\mathcal X,\mathcal Y$ and every nonempty class $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$ the following are equivalent: (i) $\mathcal H$ is realizably full-set PAC learnable; (ii) $\mathcal H$ is agnostically full-set PAC learnable with the benchmark $L^{\mathrm{set}}$ of (5); (iii) $d^\cap_{\mathrm{pack},\gamma}(\mathcal H)<\infty$. Moreover, if $d=d^\cap_{\mathrm{pack},\gamma}(\mathcal H)<\infty$ and $B=d+1+\log(2/\delta)$, then for all $\varepsilon,\delta\in(0,1)$
--   $$m^{\mathrm{full}}_{\mathcal H}(\varepsilon,\delta)\le\Big\lceil c\,\frac B\varepsilon\log^2\frac{2B}\varepsilon\Big\rceil,\qquad m^{\mathrm{full,ag}}_{\mathcal H}(\varepsilon,\delta)\le\Big\lceil c\,\frac B{\varepsilon^2}\log^2\frac{2B}\varepsilon\Big\rceil.\tag{62, 63}$$
--   These conditions imply $d^\cap_{\mathrm N}(\mathcal H)<\infty$. Finally, for $\ell\ge2$, finiteness of $d^\cap_{\mathrm{DS}}(\mathcal H)$ neither implies nor is implied by realizable full-set PAC learnability, even for total classes with at most two correct labels per input.
--
--   The packed dimension replaces the generalized Natarajan dimension when the label space is infinite, with rates that do not depend on $|\mathcal Y|$; Theorem 41 uses the equivalence for (vi).
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: ⌈·⌉ bounds on sample complexity → m(ε, δ) ≤ ((⌈x⌉₊ : ℕ) : ℕ∞); reason: Nat.ceil equals ⌈x⌉ for the positive arguments that occur
--   - encoding: a constant c depending only on ℓ and γ → ∃ c : ℝ, 0 < c placed after ∀ ℓ and γ and before ∀ X Y H (and all ε, δ, m, d); reason: the quantifier order that makes c independent of X, Y, k, H, d, m, ε, δ
--   - encoding: agnostic laws on X × A → D : PMF (X × Finset Y) with AgnLaw ℓ D; reason: Lean convention
--   - reading: "finiteness of d∩_DS(H) neither implies nor is implied by realizable full-set PAC learnability, even for total classes with at most two correct labels per input" (for ℓ ≥ 2) → two existence statements: some countable nonempty X, Y : Type and a nonempty total class with values of size ≤ 2 (and ≤ ℓ) with dsDim < ⊤ that is not FullLearnable, and one with dsDim = ⊤ that is FullLearnable; reason: the clause asserts that neither implication holds in general; it cannot hold for every fixed Y (by Theorem 16 for finite Y), and Appendix A builds such classes over countable X, Y
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 67 (PDF 69), Theorem 45, (62), (63)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_45 :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ γ : ℝ, 0 < γ → γ < 1 / ((ℓ : ℝ) + 1) → ∃ c : ℝ, 0 < c ∧
      (∀ (X Y : Type) [Countable X] [Nonempty X] [Countable Y] [Nonempty Y]
        (H : Set (Hyp X Y)), IsClass ℓ H → H.Nonempty →
        [FullLearnable H, AgnFullLearnable ℓ H, packDim ℓ γ H < ⊤].TFAE ∧
        (∀ d : ℕ, packDim ℓ γ H = d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          mFull H ε δ ≤ ((⌈c * (((d : ℝ) + 1 + Real.log (2 / δ)) / ε) *
            Real.log (2 * ((d : ℝ) + 1 + Real.log (2 / δ)) / ε) ^ 2⌉₊ : ℕ) : ℕ∞) ∧
          mFullAg ℓ H ε δ ≤ ((⌈c * (((d : ℝ) + 1 + Real.log (2 / δ)) / ε ^ 2) *
            Real.log (2 * ((d : ℝ) + 1 + Real.log (2 / δ)) / ε) ^ 2⌉₊ : ℕ) : ℕ∞)) ∧
        (packDim ℓ γ H < ⊤ → natDim H < ⊤)) ∧
      (2 ≤ ℓ →
        (∃ (X Y : Type) (_ : Countable X) (_ : Nonempty X) (_ : Countable Y) (_ : Nonempty Y)
          (H : Set (Hyp X Y)), IsClass ℓ H ∧ H.Nonempty ∧ (∀ h ∈ H, IsTotal h) ∧
          (∀ h ∈ H, ∀ x (A : Finset Y), h x = some A → A.card ≤ 2) ∧
          dsDim H < ⊤ ∧ ¬ FullLearnable H) ∧
        (∃ (X Y : Type) (_ : Countable X) (_ : Nonempty X) (_ : Countable Y) (_ : Nonempty Y)
          (H : Set (Hyp X Y)), IsClass ℓ H ∧ H.Nonempty ∧ (∀ h ∈ H, IsTotal h) ∧
          (∀ h ∈ H, ∀ x (A : Finset Y), h x = some A → A.card ≤ 2) ∧
          dsDim H = ⊤ ∧ FullLearnable H)) := by sorry

end MultiCorrectPAC.Demo
