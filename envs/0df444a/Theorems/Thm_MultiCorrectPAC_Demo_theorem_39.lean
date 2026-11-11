-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_39
-- name    : MultiCorrectPAC.Demo.theorem_39
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:46:02.187304+00:00
-- url     : https://prove2.me/theorems/e0ce5eeb-741a-4df6-9bd8-6d6c07819aab
-- title:
--   Theorem 39 — prediction families with the intersection property give a one-correct-label learner with expected loss ≤ min{1, 2((ℓ+1)(log B_N + log N)/⌊N/2⌋)^{1/ℓ} + 1/N}
-- statement:
--   Let $\mathcal H$ be a nonempty class and $N\ge2$, and suppose that families $\mathcal F_{h,S}$ with size bound $B_N$ have the intersection property of Definition 38. Then there is a one-correct-label learner that uses $N-1$ examples and outputs a randomized prediction rule $\hat p$ such that for every $h^\star\in\mathcal H$, every distribution $P$ with $P(\operatorname{supp}(h^\star))=1$ and every law $\mathcal D$ on $\mathcal X\times\mathcal Y$ with marginal $P$ compatible with $h^\star$,
--   $$\mathbb E\big[L_{P,h^\star}(\hat p)\big]\le\min\Big\{1,\ 2\Big(\frac{(\ell+1)(\log B_N+\log N)}{\lfloor N/2\rfloor}\Big)^{1/\ell}+\frac1N\Big\},\tag{45}$$
--   the expectation being over the training examples drawn from $\mathcal D$ and the seed.
--
--   This is the sufficiency half of the reduction: it turns small families of single-label predictions into a learner from demonstrations, with the exponent $1/\ell$ that Theorem 43 shows to be necessary.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: multisets S of N inputs, families F_{h,S} ⊆ {f : supp(S) → Y}, |F_{h,S}| ≤ B_N with B_N ≥ 1 → F : (S : Multiset X) → Hyp X Y → Finset ({x // x ∈ S} → Y) and HasIntersectionProperty ℓ N B H F (B ≥ 1, the size bound and (44) at card S = N for h ∈ H defined on S); reason: Lean convention; values at other S, h are unconstrained and unused
--   - encoding: E[L_{P,h⋆}(p̂)]; ⌊N/2⌋; logarithms → oneExpLoss D h A (sum over samples of the product weight times the lower integral over the seed) ≤ ENNReal.ofReal (min 1 …); ⌊N/2⌋ as the natural number N / 2; Real.log; reason: Lean convention; the loss is a [0,1]-valued measurable function of the seed
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 56 (PDF 58), Theorem 39, (45)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_PredictionFamilies

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_39 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Countable Y]
    [Nonempty Y] (H : Set (Hyp X Y)) (hH : IsClass ℓ H) (hne : H.Nonempty) (N : ℕ) (hN : 2 ≤ N)
    (B : ℕ) (F : (S : Multiset X) → Hyp X Y → Finset ({x // x ∈ S} → Y))
    (hF : HasIntersectionProperty ℓ N B H F) :
    ∃ A : RandLearner (X × Y) X Y (N - 1), ∀ h ∈ H, ∀ D : PMF (X × Y), Compatible h D →
      oneExpLoss D h A ≤ ENNReal.ofReal (min 1
        (2 * (((ℓ : ℝ) + 1) * (Real.log B + Real.log N) / ((N / 2 : ℕ) : ℝ)) ^ (1 / (ℓ : ℝ))
          + 1 / (N : ℝ))) := by sorry

end MultiCorrectPAC.Demo
