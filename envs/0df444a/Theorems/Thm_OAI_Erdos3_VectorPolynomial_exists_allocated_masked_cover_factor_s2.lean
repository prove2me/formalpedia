-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_masked_cover_factor_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_masked_cover_factor_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:50:49.908507+00:00
-- url     : https://prove2.me/theorems/9273420f-ae76-41e7-83a2-35f4770732a8
-- title:
--   The allocated masked site chart factor equals twice a buffered torus cutoff times a bounded Lipschitz function of the rescaled torus coordinates
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI). Let $o_j$ be an orthonormal basis of $U_j$ indexed by $I_j$, and assume (hypothesis $h_b$) that the $\mathbb{Z}$-span of $b_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$ for every $j$. Let $E_j$ be finite types and $bW_j$ a $\mathbb{Z}$-basis, indexed by $E_j$, of the lattice $\Gamma_j$ = the section of the standard lattice $\mathbb{Z}^{J_j}$ by $U_j$. Let $d$ and $\mathrm{period}$ be positive natural numbers and $r > 0$ a nonnegative real (hypothesis $h_r$). Let $\Phi_j$ = `normalizedOrthogonalChart` of $U_j$ and $b_j$ (the linear isomorphism $\mathbb{R}^{J_j} \cong U_j \times \mathbb{R}^{n_j}$ given by orthogonal projection onto $U_j$ and normalized $b_j$-coordinates of the projection onto the complement; defined by OpenAI).
--
--   **Hypotheses.** Assume:
--   - $\mathrm{period} \mid d$;
--   - $R_j > 0$ for all $j$;
--   - $C : \mathrm{Fin}\,m \to \mathbb{R}$ with $C_j \ge 0$, $\|\Phi_j^{-1}(v)\| \le C_j \|v\|$ for all $v$, and $C_j\,(|I_j| + 1)(2 r R_j) \le 1/4$, for all $j$;
--   - $C^{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb{R}_{\ge 0}$ with $\|\Phi_j(v)\| \le C^{\mathrm{fwd}}_j \|v\|$ for all $j, v$;
--   - $K \in \mathbb{R}_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$;
--   - $\mathrm{label} \in \bigl(\prod_j (\mathbb{Z}/\mathrm{period})^{\mathrm{Fin}(n_j)}\bigr) \times \bigl(\prod_j (\mathbb{Z}/\mathrm{period})^{E_j}\bigr)$;
--   - $f : \mathbb{R}^{\texttt{LayerSamplerAxis I n}} \to \mathbb{C}$ is $L$-Lipschitz (for some $L \in \mathbb{R}_{\ge 0}$) with $|f(z)| \le 1$ for all $z$.
--
--   **Conclusion.** There is a function $g : (\mathbb{R}/\mathbb{Z})^{\Sigma_j J_j} \to \mathbb{C}$ such that
--   - $g$ is Lipschitz with constant $\max\bigl(L \cdot (K \sum_j C^{\mathrm{fwd}}_j |J_j|) \cdot \mathrm{period},\ 4\,\mathrm{period}\bigr)$;
--   - $|g(z)| \le 1$ for all $z$;
--   - for all $u = (u_j)_j$ with $u_j \in U_j$ and every $y$ in `EuclideanJetLayers U single` (the jet layers with a single row in each layer, $\mathrm{single}_j = \mathrm{Unit}$; defined by OpenAI) such that, for every $j$, the class of $d^{-1} u_j$ in $U_j / \Gamma_j$ equals the $j$-th component $y_j$ of $y$:
--   $$\texttt{allocatedMaskedSiteChartFactor B U b S o h\_b bW d r h\_r period label f}\ y = 2 \cdot \texttt{allocatedBufferedTorusCutoff U b o r h\_r}\bigl(\texttt{coveredJetAmbientTorus U d}\ y\bigr) \cdot g\Bigl(\bigl((u_{j})_{i} / \mathrm{period} \bmod 1\bigr)_{(j, i) \in \Sigma_j J_j}\Bigr).$$
--
--   Here (all defined by OpenAI) `allocatedMaskedSiteChartFactor` is the restricted complex chart density, for the mixed covered jet chart and region with the closed quarter boxes $\{|v_i| \le 1/4\}$, of the buffered mixed site factor built from $f$, kept only where the site residue modulo $\mathrm{period}$ equals $\mathrm{label}$; `allocatedBufferedTorusCutoff` is a small-box torus kernel of a buffered ambient cutoff; and `coveredJetAmbientTorus U d y` sends $y$ to its coordinates in the ambient torus $(\mathbb{R}/\mathbb{Z})^{\texttt{JetAmbientIndex}}$ (indexed by triples: layer $j$, row, coordinate in $J_j$) after the $d$-fold integer cover.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_masked_cover_factor_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_masked_cover_factor` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B216`, `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteModelPhysicalExpansion.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_masked_cover_factor)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

theorem exists_allocated_masked_cover_factor_s2
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    ∃ g : ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith (max (L * (K * ∑ j, Cforward j * Fintype.card (J j)) * period) (4 * period)) g ∧
      (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ (u : ∀ j, euclideanSubspace (U j)) (y : EuclideanJetLayers U single),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j ()) →
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y =
          2 * (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) *
            g (fun a => (((u a.1).val a.2 / period : ℝ) : UnitAddCircle)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
