-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceTolerance_log_bound_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineSourceTolerance_log_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:05:06.852667+00:00
-- url     : https://prove2.me/theorems/8af7f98b-a6e6-4319-9a99-4a600a94c739
-- title:
--   The log of the inverse allocated affine source tolerance is bounded by the allocated affine tolerance log
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type $B_a$ to each axis $a$ of `LayerSamplerAxis I n` (the pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $\alpha$ be a finite type with decidable equality, and let $O_j$ ($j \in \operatorname{Fin} m$) be nonempty finite types. Let $A, T$ be nonnegative real numbers and $\delta, \varepsilon, E, F$ real numbers with $0 < \delta \le 1$, $\varepsilon > 0$, $E \ge 0$, $F \ge 0$, $\varepsilon^{-1} \le e^E$ and $\delta^{-1} \le e^F$.
--
--   Let $\theta$ = `allocatedAffineSourceTolerance B A T δ ε` (with the implicit parameters $G$, $O$, $\alpha$), defined by OpenAI as the minimum, over all predicates $P$ on the axes, of OpenAI's `partitionedAffineSourceTolerance` for the partition of the axes by $P$ (with variable type $G \times \operatorname{Option} \alpha$, row types $O_j$ on the axes not satisfying $P$, degrees `layerSamplerDegree I n` $(j, \cdot) \mapsto j+1$, and parameters $A, T, m, \delta, \varepsilon$). Let $\Lambda$ = `allocatedAffineToleranceLog B A T E F`, defined by OpenAI as the maximum over all predicates $P$ on the axes of OpenAI's `allocatedAffinePartitionLog B A T E F P`. Then
--   $$\log(\theta^{-1}) \le \Lambda,$$
--   where $\log$ is Mathlib's real logarithm (so $\log 0 = 0$ and $\log |x|$ is used for negative $x$; the statement does not separately assert $\theta > 0$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceTolerance_log_bound_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceTolerance_log_bound` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineSourceTolerance_log_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

 theorem allocatedAffineSourceTolerance_log_bound_s2 (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    Real.log (allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T δ ε)⁻¹ ≤
      allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
