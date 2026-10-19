-- Prove2me | Theorems.Thm_OAI_Erdos3_principalSupportedResidue_axis_marginal_s2
-- name    : OAI.Erdos3.principalSupportedResidue_axis_marginal_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:20:32.269481+00:00
-- url     : https://prove2.me/theorems/623cc781-a7a6-4381-b991-b9b566b00ddf
-- title:
--   The axis marginal of the residue-conditioned principal tuple law is a product of uniform cube source laws
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B(d)$ for $d \in D$ finite types with decidable equality, and $h : D \to \mathbb{N}$. The principal tuple index is $\Sigma_{d \in D} B(d) \times \{0, \dots, h(d) - 1\}$. Let $L$ be a positive natural-valued function on this index set; let $q > 0$ be a natural number and $r$ assign to each index $t$ a residue vector $r_t : \texttt{Option}\ \alpha \to \mathbb{Z}/q$. Fix an axis $a \in D$ and assume $(\lvert\alpha\rvert + 1)\, q \le L(a, b, v)$ for all $b \in B(a)$ and $v < h(a)$. Let $\mu$ = `principalTupleWeights B h L hL`, the product over indices $t$ of the cube laws `integerScalarCubeWeights α (L t)` on `PrincipalIntegerTuples B h α L`, and assume the residue cell $\mathcal{C} = \{y : \texttt{principalResidueLabel q}\ y = r\}$ (tuples whose coordinatewise reduction modulo $q$ equals $r$) has positive $\mu$-mass.
--
--   Then the push-forward of the conditioned law $\mu(\cdot \mid \mathcal{C})$ (as a PMF) under the map $y \mapsto \bigl((b, v) \mapsto y(a, b, v)\bigr)$, which restricts a tuple to the indices on axis $a$, equals the product PMF
--   $$\texttt{dependentProductPMF}\Bigl(b \mapsto \texttt{dependentProductPMF}\bigl(v \mapsto \sigma_{b,v}\bigr)\Bigr),$$
--   where $\sigma_{b,v}$ is the PMF of the source law of `principalSupportedAxisSources B h L hL q hq r a hsize b v` $=$ `normalizedUniformCubeSource α (L ⟨a,b,v⟩) q … (fun _ => q) (r ⟨a,b,v⟩) …` (OpenAI: a normalized scalar cube source of length $L(a, b, v)$, every modulus equal to $q$, residues $r_{(a,b,v)}$, and constant weight $1$), and `dependentProductPMF` is the product of a finite family of PMFs.
--
--   Lean: `OAI.Erdos3.principalSupportedResidue_axis_marginal_s2`, which states OpenAI's `OAI.Erdos3.principalSupportedResidue_axis_marginal` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedResidueInterpolationMixture.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B126`, `OAIE3v2B136` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedResidueInterpolationMixture.lean (declaration OAI.Erdos3.principalSupportedResidue_axis_marginal)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B136

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem principalSupportedResidue_axis_marginal_s2 :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (fun b => dependentProductPMF (fun v => ((sources) b v).source.toPMF)) := by
  sorry

end Erdos3

end

end OAI
end
