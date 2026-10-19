-- Prove2me | Theorems.Thm_OAI_Erdos3_principalSupportedResidue_selected_kernels_s2
-- name    : OAI.Erdos3.principalSupportedResidue_selected_kernels_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:59:52.154687+00:00
-- url     : https://prove2.me/theorems/e1414acc-7610-42a6-b64b-3faf9044c470
-- title:
--   Under the residue-conditioned principal tuple law, kernels applied to distinct selected blocks are independent
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B_d$ ($d \in D$) finite types with decidable equality, and $h : D \to \mathbb{N}$. Write $\mathcal{P}$ = `PrincipalTupleIndex B h` $= \Sigma_{d}\, B_d \times \mathrm{Fin}(h_d)$. Let $L : \mathcal{P} \to \mathbb{N}$ with $L_t > 0$ for all $t$. A principal tuple $y$ (`PrincipalIntegerTuples B h α L`) assigns to each $t \in \mathcal{P}$ an integer point $y_t$ of OpenAI's scalar cube box `IntegerScalarCubeBox α (L t)` (integer arrays indexed by $\mathrm{Option}\ \alpha$). Let `principalTupleWeights B h L hL` be OpenAI's product probability weights on tuples (the product over $t$ of `integerScalarCubeWeights α (L t)`). Let $q$ be a natural number and $r : \mathcal{P} \to \mathrm{Option}\ \alpha \to \mathbb{Z}/q\mathbb{Z}$, and assume that the set of tuples $y$ with `principalResidueLabel q y = r` (that is, $y_t(i) \bmod q = r_t(i)$ for all $t, i$) has positive mass. Let $\pi$ be the probability mass function of the weights conditioned on this set.
--
--   Let $A$ be a finite type and $e : A \to D$ injective. For each $a \in A$ let $Y_a$ be a countable measurable space with measurable singletons, and let $k_a$ be a map from block data $(b, v) \mapsto$ a point of `IntegerScalarCubeBox α (L ⟨e a, b, v⟩)` (for $b \in B_{e(a)}$, $v \in \mathrm{Fin}(h_{e(a)})$) to probability mass functions on $Y_a$. Then
--   $$\pi.\mathrm{bind}\Bigl(y \mapsto \textstyle\prod_{a}^{\mathrm{dep}} k_a\bigl((b, v) \mapsto y_{\langle e(a), b, v\rangle}\bigr)\Bigr) = \textstyle\prod_{a}^{\mathrm{dep}} \Bigl(\pi.\mathrm{bind}\bigl(y \mapsto k_a((b, v) \mapsto y_{\langle e(a), b, v\rangle})\bigr)\Bigr),$$
--   where $\prod^{\mathrm{dep}}_a p_a$ = `dependentProductPMF p` is the product probability mass function on $\prod_a Y_a$, with mass $\prod_a p_a(x_a)$ at $x$. In words: drawing $y$ from the conditioned law and then independently applying $k_a$ to the block of $y$ at $e(a)$ gives the same law as drawing each coordinate $a$ from its own marginal, independently.
--
--   Lean: `OAI.Erdos3.principalSupportedResidue_selected_kernels_s2`, which states OpenAI's `OAI.Erdos3.principalSupportedResidue_selected_kernels` (in `lean/OAI/Combinatorics/Progressions/Linear/ContainedSupportedProgressionKernels.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B111` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/ContainedSupportedProgressionKernels.lean (declaration OAI.Erdos3.principalSupportedResidue_selected_kernels)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B111

section

namespace OAI

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidue_selected_kernels_s2 {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (k : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a, b, v⟩)) →
      PMF (Y a)) :
    (conditioned).toPMF.bind (fun y => dependentProductPMF
      (fun a => k a (fun b v => y ⟨e a, b, v⟩))) =
      dependentProductPMF (fun a => (conditioned).toPMF.bind
        (fun y => k a (fun b v => y ⟨e a, b, v⟩))) := by
  sorry

end Erdos3

end

end OAI
end
