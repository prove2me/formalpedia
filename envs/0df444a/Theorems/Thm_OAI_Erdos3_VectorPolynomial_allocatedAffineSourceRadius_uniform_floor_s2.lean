-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceRadius_uniform_floor_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:43:19.613303+00:00
-- url     : https://prove2.me/theorems/5ac50ab1-35e7-4692-bbc7-f0234140e87f
-- title:
--   A uniform lower bound exp(-allocatedAffineRadiusLog) for the partitioned affine source radii over all partitions
-- statement:
--   Let $m$ be a natural number, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, and $B$ a family of finite types indexed by `LayerSamplerAxis I n` $= \Sigma_{j}\, (I\ j \oplus \mathrm{Fin}\ (n\ j))$. Let $\alpha$ be a finite type with decidable equality and $O : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite nonempty types. Let $A, T \in \mathbb{R}_{\ge 0}$ and let $\delta, \varepsilon, E, F$ be real numbers with $0 < \delta \le 1$, $0 < \varepsilon$, $0 \le E$, $0 \le F$, $\varepsilon^{-1} \le e^{E}$ and $\delta^{-1} \le e^{F}$.
--
--   Let $\rho$ assign to every predicate $P$ on `LayerSamplerAxis I n` a number $\rho(P) \in \mathbb{R}_{\ge 0}$, such that for every $P$: $\rho(P) > 0$, and
--   $$\rho(P) = \texttt{partitionedAffineSourceRadius}\ (\texttt{layerSamplerDegree I n})\ P\ A\ T\ \delta\ \varepsilon,$$
--   where `partitionedAffineSourceRadius` is an explicit real-valued radius defined by OpenAI, here taken with the axis family $B$, the output types $a \mapsto O_{j}$ for each axis $a = \langle j, \cdot\rangle$ not satisfying $P$, and the type $\alpha$; and `layerSamplerDegree I n` assigns to the axis $\langle j, \cdot \rangle$ the degree $j + 1$.
--
--   Then for every predicate $P$ on `LayerSamplerAxis I n`,
--   $$\exp\bigl(-\texttt{allocatedAffineRadiusLog}\ B\ A\ T\ E\ F\bigr) \le \rho(P),$$
--   where `allocatedAffineRadiusLog B A T E F` (with output types $O$ and the type $\alpha$) is the maximum over all predicates $P'$ on `LayerSamplerAxis I n` of an explicit logarithmic budget `allocatedAffinePartitionRadiusLog` defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B112` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineSourceRadius_uniform_floor)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

 theorem allocatedAffineSourceRadius_uniform_floor_s2 (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρ : ∀ P, 0 < ρ P)
    (hρeq : ∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) :
    ∀ P, Real.exp (-allocatedAffineRadiusLog (O := O) (α := α) B A T E F) ≤ ρ P := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
