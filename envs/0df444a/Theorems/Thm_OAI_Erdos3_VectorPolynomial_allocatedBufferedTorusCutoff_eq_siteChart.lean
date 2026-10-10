-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedTorusCutoff_eq_siteChart
-- name    : OAI.Erdos3.VectorPolynomial.allocatedBufferedTorusCutoff_eq_siteChart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:36:09.651663+00:00
-- url     : https://prove2.me/theorems/d3cc5260-e8d6-432e-982d-07a1ecfac0fe
-- title:
--   The buffered torus cutoff of a covered jet equals the buffered site-chart factor
-- statement:
--   Fix $m \in \mathbb N$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$, reals $R_j > 0$, and a nonnegative real $r > 0$. Let $C_j \ge 0$ be reals such that, for every $j$ and $v$, the inverse of the continuous linear equivalence `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` satisfies $\|\cdot^{-1}(v)\| \le C_j\|v\|$, and $C_j\bigl((|I_j|+1)(2 r R_j)\bigr) \le 1/4$. Let $G$ be a finite type, $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), $\sigma_j$ reals, and $S$ a `LayerSamplerScale` for $(B, U, b, R, \sigma)$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Assume ($h_b$) that the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$; let $E_j$ be finite types, $bW_j$ a $\mathbb Z$-basis indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), and $d \ne 0$ a natural number. Then for every $y \in$ `EuclideanJetLayers U (fun _ => Unit)` (one point of each quotient of `euclideanSubspace (U j)` by its integer lattice section),
--   $$\texttt{allocatedBufferedTorusCutoff}\ U\ b\ o\ r\ h_r\ (\texttt{coveredJetAmbientTorus}\ U\ d\ y) = \texttt{allocatedBufferedSiteChartFactor}\ B\ U\ b\ S\ o\ h_b\ bW\ d\ r\ h_r\ (\_ \mapsto 1)\ y,$$
--   the left side (a real number, with $R$ implicit) cast to $\mathbb C$; here `coveredJetAmbientTorus U d y` is a point of the torus $(\mathbb R/\mathbb Z)^{\Sigma_j\, \mathrm{Unit} \times J_j}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedBufferedTorusCutoff_eq_siteChart` in `lean/OAI/Combinatorics/Progressions/Fourier/AllocatedNormalizedTorusCutoff.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B054`, `OAIErdos3B150` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/AllocatedNormalizedTorusCutoff.lean#L71

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B150

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_eq_siteChart
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) =
      allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
