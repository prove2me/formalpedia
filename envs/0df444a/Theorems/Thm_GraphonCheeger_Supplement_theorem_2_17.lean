-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_2_17
-- name    : GraphonCheeger.Supplement.theorem_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:24:43.224359+00:00
-- url     : https://prove2.me/theorems/1effe287-0af0-4de9-843e-84b3147ab2b0
-- title:
--   Theorem 2.17 — equivalent pure coloured graphons on $[0,1]$ have a common pullback
-- statement:
--   Let $(W,\chi)$ and $(\widetilde W,\tilde\chi)$ be pure coloured graphons on $[0,1]$ with Lebesgue measure such that $(W,\chi)\cong(\widetilde W,\tilde\chi)$. Then there exist measure-preserving maps $\varphi,\tilde\varphi:[0,1]\to[0,1]$ such that
--   $$
--   W\bigl(\varphi(x),\varphi(y)\bigr)=\widetilde W\bigl(\tilde\varphi(x),\tilde\varphi(y)\bigr)\ \text{ for a.e. }(x,y)\in[0,1]^2,\qquad
--   \chi(\varphi(x))=\tilde\chi(\tilde\varphi(x))\ \text{ for a.e. }x\in[0,1].
--   $$
--
--   This extends to pure coloured graphons Theorem A.1(ii) (Bollobás–Riordan): equivalent uncoloured graphons on $[0,1]$ have a common pullback. The paper shows that no such statement holds for mixed colourings.
--
--   **Formalization Note** The pullback of a coloured graphon is $(W,\chi)^\varphi=(W^\varphi,\chi\circ\varphi)$ (p.11), so "$W^\varphi=\widetilde W^{\tilde\varphi}$ a.e." is the pair of a.e. equalities above. The maps need not be bijective.
--
--   Differences from the source:
--   - encoding: [0, 1] with Lebesgue measure λ → unitInterval with volume and the Borel σ-field; reason: Remark 3.3: the Borel and Lebesgue σ-fields give the same results up to a.e. equality
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
--   - encoding: W₁ ≅ W₂ (Definition 2.6: one, and thus all, of the conditions of Lemma 2.5) → CEquiv: t(F, W₁) = t(F, W₂) for every coloured graph F; reason: condition (i) of Lemma 2.5, which Definition 2.6 lists as equivalent to the others
--   - encoding: (W, χ)^φ = (W̃, χ̃)^φ̃ a.e. → W ∘ (φ × φ) = W̃ ∘ (φ̃ × φ̃) a.e. on [0, 1]² and χ ∘ φ = χ̃ ∘ φ̃ a.e. on [0, 1]; reason: (W, χ)^φ = (W^φ, χ ∘ φ) (p.11) and a.e. equality of coloured graphons is a.e. equality of both components (Remark 3.3)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 2.17, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 2.17, p.11 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `(W, χ)` and `(W̃, χ̃)` be pure coloured graphons on `[0, 1]` with
`(W, χ) ≅ (W̃, χ̃)`. Then there exist measure-preserving maps `φ, φ̃ : [0, 1] → [0, 1]` with
`(W, χ)^φ = (W̃, χ̃)^φ̃` a.e.

**Formalization Note.** `[0, 1]` carries Lebesgue measure (`volume` on `unitInterval`). The
pullback `(W, χ)^φ = (W^φ, χ ∘ φ)` (p.11), so the conclusion is `W^φ = W̃^φ̃` a.e. on `[0, 1]²` and
`χ ∘ φ = χ̃ ∘ φ̃` a.e. on `[0, 1]`. A pure colouring is a measurable `χ : [0, 1] → [κ]`, entering the
equivalence through its point-mass colouring `ofColour χ`. The maps need not be bijective. -/
theorem theorem_2_17 {κ : ℕ} (W W' : unitInterval → unitInterval → ℝ) (hW : IsGraphon W)
    (hW' : IsGraphon W') (χ χ' : unitInterval → Fin κ) (hχ : Measurable χ) (hχ' : Measurable χ')
    (hequiv : CEquiv volume W (ofColour χ) volume W' (ofColour χ')) :
    ∃ φ φ' : unitInterval → unitInterval,
      MeasurePreserving φ volume volume ∧ MeasurePreserving φ' volume volume ∧
      (∀ᵐ p ∂((volume : Measure unitInterval).prod volume),
        W (φ p.1) (φ p.2) = W' (φ' p.1) (φ' p.2)) ∧
      (∀ᵐ x ∂(volume : Measure unitInterval), χ (φ x) = χ' (φ' x)) := by sorry

end GraphonCheeger.Supplement
