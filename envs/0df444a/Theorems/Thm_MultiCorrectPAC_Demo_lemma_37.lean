-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_37
-- name    : MultiCorrectPAC.Demo.lemma_37
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:33.093453+00:00
-- url     : https://prove2.me/theorems/09497415-019b-4662-9760-a39a67ee0b86
-- title:
--   Lemma 37 — common demonstrations: m^full_{I_R(H)}(ε, δ) ≤ m^one_H(ε/R, δ/R)
-- statement:
--   For every class $\mathcal H$, every integer $R\ge1$ and $\varepsilon,\delta\in(0,1)$,
--   $$m^{\mathrm{full}}_{\mathcal I_R(\mathcal H)}(\varepsilon,\delta)\le m^{\mathrm{one}}_{\mathcal H}(\varepsilon/R,\delta/R).$$
--
--   A label in $h_1(x)\cap\dots\cap h_r(x)$ is a valid demonstration for each $h_a$; this is the necessity half of the reduction between one-correct-label learning of $\mathcal H$ and full-set learning of $\mathcal I_{\ell+1}(\mathcal H)$.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: I_R(H) of (7): g = ⋂ₐ hₐ on any B ⊆ ⋂ₐ supp(hₐ) where the intersection is nonempty, ⋆ off B, 1 ≤ r ≤ R → interClass R H: ∃ r ∈ [1, R], hs : Fin r → H with g x = none or g x = some A, A nonempty, A = {y : ∀ a, y ∈ hs a x}; reason: B is supp(g); nonemptiness of the intersection forces every hₐ to be defined on B
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 55 (PDF 57), Lemma 37

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_37 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Countable Y]
    [Nonempty Y] (H : Set (Hyp X Y)) (hH : IsClass ℓ H) (R : ℕ) (hR : 1 ≤ R) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    mFull (interClass R H) ε δ ≤ mOne H (ε / R) (δ / R) := by sorry

end MultiCorrectPAC.Demo
