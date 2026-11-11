-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_41
-- name    : MultiCorrectPAC.Demo.theorem_41
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:55.677471+00:00
-- url     : https://prove2.me/theorems/055862ff-37d6-440f-8172-88047e518266
-- title:
--   Theorem 41 (Theorem B, stronger form) — finite labels: one-correct-label learnability of H ⇔ full-set learnability of I_{ℓ+1}(H) ⇔ finiteness of its four dimensions, with rates (54), (55)
-- statement:
--   Let $\ell\ge1$. There is a constant $c>0$ depending only on $\ell$ such that the following holds. Let $\mathcal X$ be a nonempty countable set, $\mathcal Y$ a finite set with $k=|\mathcal Y|\ge\ell$, and $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$ nonempty. For every $0<\gamma<1/(\ell+1)$ the following are equivalent:
--   (i) $\mathcal H$ is realizably one-correct-label PAC learnable; (ii) $\mathcal I_{\ell+1}(\mathcal H)$ is realizably full-set PAC learnable; (iii) $d^\cap_{\mathrm N}(\mathcal I_{\ell+1}(\mathcal H))<\infty$; (iv) $d^\cap_{\mathrm{DS}}(\mathcal I_{\ell+1}(\mathcal H))<\infty$; (v) $d_{\mathrm{pair}}(\mathcal I_{\ell+1}(\mathcal H))<\infty$; (vi) $d^\cap_{\mathrm{pack},\gamma}(\mathcal I_{\ell+1}(\mathcal H))<\infty$.
--
--   Moreover, let $d=d^\cap_{\mathrm N}(\mathcal I_{\ell+1}(\mathcal H))<\infty$. (a) For every $m\ge1$ there is a learner that uses $m$ one-correct-label examples and outputs a randomized prediction rule $\hat p_m$ with
--   $$\mathbb E\big[L_{P,h^\star}(\hat p_m)\big]\le\min\Big\{1,\ c\Big[\frac{(d+1)\log^2(2(m+1)(k+1))}{m+1}\Big]^{1/\ell}\Big\}\tag{54}$$
--   for every $h^\star\in\mathcal H$ and every law $\mathcal D$ compatible with $h^\star$ whose marginal $P$ satisfies $P(\operatorname{supp}(h^\star))=1$ (expectation over the examples and the seed). (b) For all $\varepsilon,\delta\in(0,1)$
--   $$m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)\le\Big\lceil c\,(d+1)\,\varepsilon^{-\ell}\log^2\frac{(d+2)(k+1)}{\varepsilon}\log\frac2\delta\Big\rceil.\tag{55}$$
--   Both bounds also hold with $d^\cap_{\mathrm{DS}}(\mathcal I_{\ell+1}(\mathcal H))$ in place of $d$, and if $d=0$, then $m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)=0$.
--
--   Learning from one correct label is exactly full-set learning of the class of $(\ell+1)$-fold partial intersections: a demonstration cannot distinguish hypotheses whose correct-label sets share it. The rate $\tilde O(d\,\varepsilon^{-\ell})$ is optimal in its exponent (Theorem 43).
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: X nonempty countable, |Y| = k < ∞, ℓ ≤ k (§5.1) → X : Type with [Countable X] [Nonempty X]; Y : Type with [Fintype Y], k = Fintype.card Y, ℓ ≤ Fintype.card Y; hℓ : 1 ≤ ℓ; reason: the standing assumptions made explicit (a finite Y with k ≥ ℓ ≥ 1 is nonempty)
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: ⌈·⌉ bounds on sample complexity → m(ε, δ) ≤ ((⌈x⌉₊ : ℕ) : ℕ∞); reason: Nat.ceil equals ⌈x⌉ for the positive arguments that occur
--   - encoding: I_R(H) of (7): g = ⋂ₐ hₐ on any B ⊆ ⋂ₐ supp(hₐ) where the intersection is nonempty, ⋆ off B, 1 ≤ r ≤ R → interClass R H: ∃ r ∈ [1, R], hs : Fin r → H with g x = none or g x = some A, A nonempty, A = {y : ∀ a, y ∈ hs a x}; reason: B is supp(g); nonemptiness of the intersection forces every hₐ to be defined on B
--   - encoding: a constant c depending only on ℓ → ∃ c : ℝ, 0 < c placed after ∀ ℓ and before ∀ X Y H (and all ε, δ, m, d); reason: the quantifier order that makes c independent of X, Y, k, H, d, m, ε, δ
--   - encoding: the six conditions, for the fixed γ of (9) → ∀ γ with 0 < γ < 1/(ℓ+1), List.TFAE of the six propositions; reason: the paper fixes an arbitrary γ in this range
--   - encoding: "let d = d∩_N(I_{ℓ+1}(H)) < ∞ … both bounds also hold with d∩_DS(I_{ℓ+1}(H)) in place of d" → ∀ d : ℕ, (natDim (I) = d ∨ dsDim (I) = d) → (54) ∧ (55); reason: both readings of d at once
--   - encoding: E[L_{P,h⋆}(p̂_m)]; ε^{−ℓ} → oneExpLoss D h A ≤ ENNReal.ofReal (min 1 …) for A : RandLearner (X × Y) X Y m; (ε ^ ℓ)⁻¹; reason: Lean convention
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 61 (PDF 63), Theorem 41, (54), (55); Theorem B pp. 7–8 (PDF 9–10)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_41 :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ, 0 < c ∧
      ∀ (X Y : Type) [Countable X] [Nonempty X] [Fintype Y], ℓ ≤ Fintype.card Y →
      ∀ H : Set (Hyp X Y), IsClass ℓ H → H.Nonempty →
        (∀ γ : ℝ, 0 < γ → γ < 1 / ((ℓ : ℝ) + 1) →
          [OneLearnable H,
           FullLearnable (interClass (ℓ + 1) H),
           natDim (interClass (ℓ + 1) H) < ⊤,
           dsDim (interClass (ℓ + 1) H) < ⊤,
           pairDim (interClass (ℓ + 1) H) < ⊤,
           packDim ℓ γ (interClass (ℓ + 1) H) < ⊤].TFAE) ∧
        (∀ d : ℕ, (natDim (interClass (ℓ + 1) H) = d ∨ dsDim (interClass (ℓ + 1) H) = d) →
          (∀ m : ℕ, 1 ≤ m → ∃ A : RandLearner (X × Y) X Y m,
            ∀ h ∈ H, ∀ D : PMF (X × Y), Compatible h D →
              oneExpLoss D h A ≤ ENNReal.ofReal (min 1 (c *
                (((d : ℝ) + 1) * Real.log (2 * ((m : ℝ) + 1) * ((Fintype.card Y : ℝ) + 1)) ^ 2
                  / ((m : ℝ) + 1)) ^ (1 / (ℓ : ℝ))))) ∧
          (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            mOne H ε δ ≤ ((⌈c * ((d : ℝ) + 1) * (ε ^ ℓ)⁻¹ *
              Real.log (((d : ℝ) + 2) * ((Fintype.card Y : ℝ) + 1) / ε) ^ 2 *
                Real.log (2 / δ)⌉₊ : ℕ) : ℕ∞))) ∧
        (natDim (interClass (ℓ + 1) H) = 0 →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → mOne H ε δ = 0) := by sorry

end MultiCorrectPAC.Demo
