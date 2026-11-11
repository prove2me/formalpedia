-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_55
-- name    : MultiCorrectPAC.Demo.theorem_55
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:59.993733+00:00
-- url     : https://prove2.me/theorems/807c858e-46c9-4365-a1b5-62d0a39daed7
-- title:
--   Theorem 55 (Theorem E) — countable labels: one-correct-label learnability ⇔ full-set learnability of I_{ℓ+1}(H) ⇔ d∩_pack,γ(I_{ℓ+1}(H)) < ∞, rate (75)
-- statement:
--   Fix $\ell\ge1$ and $\gamma$ with $0<\gamma<1/(\ell+1)$. There is $c>0$ depending only on $\ell$ and $\gamma$ such that, for countable $\mathcal X,\mathcal Y$ and every nonempty class $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$: (i) $\mathcal H$ is realizably one-correct-label PAC learnable, (ii) $\mathcal I_{\ell+1}(\mathcal H)$ is realizably full-set PAC learnable, and (iii) $d^\cap_{\mathrm{pack},\gamma}(\mathcal I_{\ell+1}(\mathcal H))<\infty$ are equivalent, and they imply $d^\cap_{\mathrm N}(\mathcal I_{\ell+1}(\mathcal H))<\infty$. If $p=d^\cap_{\mathrm{pack},\gamma}(\mathcal I_{\ell+1}(\mathcal H))<\infty$, then for all $\varepsilon,\delta\in(0,1)$
--   $$m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)\le\big\lceil c\,(p+1)\,\varepsilon^{-\ell}\log^2(2/\varepsilon)\log(2/\delta)\big\rceil,\tag{75}$$
--   and if $p=0$ then $m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)=0$.
--
--   This extends Theorem 41 to infinite label spaces with a rate independent of $|\mathcal Y|$.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: ⌈·⌉ bounds on sample complexity → m(ε, δ) ≤ ((⌈x⌉₊ : ℕ) : ℕ∞); reason: Nat.ceil equals ⌈x⌉ for the positive arguments that occur
--   - encoding: I_R(H) of (7): g = ⋂ₐ hₐ on any B ⊆ ⋂ₐ supp(hₐ) where the intersection is nonempty, ⋆ off B, 1 ≤ r ≤ R → interClass R H: ∃ r ∈ [1, R], hs : Fin r → H with g x = none or g x = some A, A nonempty, A = {y : ∀ a, y ∈ hs a x}; reason: B is supp(g); nonemptiness of the intersection forces every hₐ to be defined on B
--   - encoding: a constant c depending only on ℓ and γ → ∃ c : ℝ, 0 < c placed after ∀ ℓ and γ and before ∀ X Y H (and all ε, δ, m, d); reason: the quantifier order that makes c independent of X, Y, k, H, d, m, ε, δ
--   - encoding: ε^{−ℓ} → (ε ^ ℓ)⁻¹; reason: Lean convention
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 76–77 (PDF 78–79), Theorem 55, (75)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_55 :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ γ : ℝ, 0 < γ → γ < 1 / ((ℓ : ℝ) + 1) → ∃ c : ℝ, 0 < c ∧
      ∀ (X Y : Type) [Countable X] [Nonempty X] [Countable Y] [Nonempty Y]
        (H : Set (Hyp X Y)), IsClass ℓ H → H.Nonempty →
        [OneLearnable H, FullLearnable (interClass (ℓ + 1) H),
          packDim ℓ γ (interClass (ℓ + 1) H) < ⊤].TFAE ∧
        (packDim ℓ γ (interClass (ℓ + 1) H) < ⊤ → natDim (interClass (ℓ + 1) H) < ⊤) ∧
        (∀ p : ℕ, packDim ℓ γ (interClass (ℓ + 1) H) = p →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            mOne H ε δ ≤ ((⌈c * ((p : ℝ) + 1) * (ε ^ ℓ)⁻¹ * Real.log (2 / ε) ^ 2 *
              Real.log (2 / δ)⌉₊ : ℕ) : ℕ∞)) ∧
        (packDim ℓ γ (interClass (ℓ + 1) H) = 0 →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → mOne H ε δ = 0) := by sorry

end MultiCorrectPAC.Demo
