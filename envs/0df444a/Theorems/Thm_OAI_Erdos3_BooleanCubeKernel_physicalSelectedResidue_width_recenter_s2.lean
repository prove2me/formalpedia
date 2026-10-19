-- Prove2me | Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_physicalSelectedResidue_width_recenter_s2
-- name    : OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:08:15.684174+00:00
-- url     : https://prove2.me/theorems/ee643030-ad5b-43f7-a385-e1d96e731561
-- title:
--   Replacing a selected-residue smooth sample by residue-cell recentered smooth samples in physical cube coordinates costs O(card/ρ)
-- statement:
--   Let $K$ and $X$ be finite types and $\alpha$ a type. Let $\mathrm{root} : K \to \mathbb{Z}$, let $D$ be an integer matrix with rows indexed by $\alpha$ and columns by $K$, and let $\mathrm{base} : X \to \mathbb{Z}$. Let $q : X \to \mathbb{N}$ with $q(x) > 0$ for every $x$, and let $T$ be a finite set of column residue patterns, i.e. of functions $r$ assigning to each $(k, x) \in \operatorname{Option} K \times X$ a residue $r(k,x) \in \mathbb{Z}/q(x)$ (`ColumnResiduePattern (Option K) X q`, defined by OpenAI). Let $V : \operatorname{Option} K \times X \to \mathbb{R}$ with $V(z) > 0$ for every $z$.
--
--   Write $\psi$ for OpenAI's `smoothProbabilityProfile`, the normalized smooth bump on $\mathbb{R}$ (integral $1$, supported in $[-3/4, 3/4]$), and $\Psi(y) = \prod_{i} \psi(y_i)$ for its product (`smoothProductProfile`). The weight `selectedResidueSmoothWeight q T V` (defined by OpenAI) sends $z : \operatorname{Option} K \times X \to \mathbb{Z}$ to $\Psi\bigl(i \mapsto z(i)/V(i)\bigr)$ if the pattern $i = (k,x) \mapsto z(i) \bmod q(x)$ lies in $T$, and to $0$ otherwise. Assume its sum over all $z$ is positive (hypothesis `hmass`), and let $P$ = `selectedResidueSmoothPMF q T V hV hmass` be the probability mass function on $\operatorname{Option} K \times X \to \mathbb{Z}$ obtained by normalizing this weight. Let $A$ = `probabilityProfileLipschitz`, a fixed nonnegative real constant chosen by OpenAI with $A \ge 1$ such that $\psi$ is $A$-Lipschitz. Let $W$ = `residueProfileWidth q V`, i.e. $W(k,x) = V(k,x)/q(x)$, and let $\rho$ be a real number with $8A \le \rho$ and $\rho \le W(z)$ for every $z$. Let $Q$ = `smoothProductPMF W _` be the probability mass function on $\operatorname{Option} K \times X \to \mathbb{Z}$ proportional to $z \mapsto \Psi\bigl(i \mapsto z(i)/W(i)\bigr)$ (defined by OpenAI). For $r \in T$ let $c_r$ = `selectedResidueCellWeight q T V r` be the ratio of $\sum_z w_r(z)$ to $\sum_z \texttt{selectedResidueSmoothWeight q T V}\ z$, where $w_r(z) = \Psi(i \mapsto z(i)/V(i))$ if $q(x) \mid z(k,x) - \tilde r(k,x)$ for all $(k,x)$ and $0$ otherwise, $\tilde r$ being some integer lift of $r$ (OpenAI's `columnResidueRepresentative`); and let $\bar r$ = `boundedColumnResidueRepresentative q r`, i.e. $\bar r(k,x) = \tilde r(k,x) \bmod q(x)$ (the integer remainder in $[0, q(x))$).
--
--   The physical cube maps are defined by OpenAI as follows. `physicalCubeRootDifferences root D base z` is the function $X \to (\mathrm{Unit} \sqcup \alpha) \to \mathbb{Z}$ sending $(x, \ast)$ to $\mathrm{base}(x) + z(\mathrm{none}, x) + \sum_{k \in K} \mathrm{root}(k)\, z(\mathrm{some}\ k, x)$ and $(x, i)$ for $i \in \alpha$ to $\sum_{k \in K} D_{i,k}\, z(\mathrm{some}\ k, x)$. For an integer function $\mathrm{res}$ on $\operatorname{Option} K \times X$, `physicalCubeResidueCoordinates root D base res q z` sends $(x, i)$ to $\texttt{physicalCubeRootDifferences root D base res}\ x\ i + q(x) \cdot \texttt{physicalCubeRootDifferences root D 0 z}\ x\ i$.
--
--   Let $\varphi : (X \to (\mathrm{Unit} \sqcup \alpha) \to \mathbb{Z}) \to \mathbb{C}$, and let $B, Z$ be real numbers with $B \ge 0$, $\|\varphi(v)\| \le B$ for all $v$, and $Z > 0$. Then
--   $$\left\| \frac{\sum_{z} P(z)\, \varphi\bigl(\texttt{physicalCubeRootDifferences root D base}\ z\bigr)}{Z} - \frac{\sum_{r \in T} c_r \sum_{z} Q(z)\, \varphi\bigl(\texttt{physicalCubeResidueCoordinates root D base}\ \bar r\ q\ z\bigr)}{Z} \right\| \le \frac{B \cdot \bigl(24\, A \cdot \#(\operatorname{Option} K \times X) / \rho\bigr)}{Z},$$
--   where the sums over $z$ are (unconditional) sums over all $z : \operatorname{Option} K \times X \to \mathbb{Z}$, the probabilities $P(z), Q(z)$ are taken as real numbers and cast to $\mathbb{C}$, and $\#$ denotes cardinality.
--
--   Lean: `OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter_s2`, which states OpenAI's `OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter` (in `lean/OAI/Combinatorics/Progressions/Lattices/PhysicalResidueOffsetShift.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/PhysicalResidueOffsetShift.lean (declaration OAI.Erdos3.BooleanCubeKernel.physicalSelectedResidue_width_recenter)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_width_recenter_s2 {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    {ρ : ℝ} (hρ : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hwidth : ∀ z, ρ ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X) / ρ)) / Z := by
  sorry

end Erdos3.BooleanCubeKernel

end

end OAI
end
