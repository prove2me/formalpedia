-- Prove2me | Theorems.Thm_OAI_Erdos3_goodKernelUniformCandidate_spec_s2
-- name    : OAI.Erdos3.goodKernelUniformCandidate_spec_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:35:49.084276+00:00
-- url     : https://prove2.me/theorems/7bab798d-58d3-4544-b5d0-405367ec2f48
-- title:
--   The uniform kernel period candidate of a good scalar kernel tuple is a period of every pivot image and of every bounded-degree integer jet
-- statement:
--   Let $\alpha$ and $J$ be finite types ($\alpha$ with decidable equality), let $L, B$ be natural numbers and $\kappa$ a real number. Let `selection` be an injective map $\alpha \hookrightarrow J$, and let $x : J \to$ `IntegerScalarCubeBox α L`, i.e. each $x_j$ is a function from $\mathrm{Option}\,\alpha$ (the elements of $\alpha$ together with one extra point, written none) to the integers in $[-L, L)$. Let $D$ = `scalarCubeDifferenceMatrix x` be the integer $\alpha \times J$ matrix with entries $D_{i,j} = x_j(i)$ (the entries at the points of $\alpha$, defined by OpenAI). Assume `GoodScalarKernelTuple selection κ B x` (defined by OpenAI): $\kappa < |\det(D')| / L^{|\alpha|}$, where $D'$ is the $\alpha \times \alpha$ submatrix of $D$ whose columns are the selected ones $\mathrm{selection}(i)$, and there is a natural number $a$ with $0 < a \le B$ such that $a\,\mathbb{Z}^{\alpha}$ is contained in the image $D(\mathbb{Z}^{J})$. Let $h$ = `height` be a natural number.
--
--   Let `goodKernelUniformCandidate selection x hx height` be the element of $\{0, \dots, B-1\}$ defined by OpenAI as $a - 1$, where $a$ is the witness of the bounded period in the second part of the hypothesis (chosen by the axiom of choice), and let $\mathrm{period}$ = `kernelPeriodCandidate (h+1) (goodKernelUniformCandidate selection x hx h)` $= a^{h+1}$ (this is how OpenAI defines `kernelPeriodCandidate`: for an element $b$ of $\{0, \dots, B-1\}$ it is $(b+1)^{\mathrm{degree}}$). Then both of the following hold.
--
--   1. For every $\mathrm{root} : J \to \mathbb{Z}$, the lattice $\mathrm{period}\cdot\mathbb{Z}^{\mathrm{Option}\,\alpha}$ is contained in `pivotFullImage P F`, the sum of the images (over $\mathbb{Z}$) of the matrices $P$ = `selectedSpatialPivot root D selection` and $F$ = `selectedSpatialFreeColumns root D selection`. Here (definitions of OpenAI) $P$ is the square block matrix with rows and columns indexed by $\mathrm{Option}\,\alpha$ whose first row is $(1, \mathrm{root}(\mathrm{selection}(i))_{i \in \alpha})$ and whose remaining block is $(0 \mid D')$, and $F$ has one column for each $j \in J$ not in the range of selection, equal to $(\mathrm{root}(j), (D_{i,j})_{i \in \alpha})$.
--   2. For every finite type $O$, every natural number $\mathrm{degree} \le h+1$, and every injective map $\mathrm{rows} : O \to \mathrm{Finset}\,\alpha$ with $|\mathrm{rows}(o)| \le \mathrm{degree}$ for all $o$, the lattice $\mathrm{period}\cdot\mathbb{Z}^{O}$ is contained in the image (over $\mathbb{Z}$) of the integer matrix `scalarKernelIntegerJet x degree rows`. This is an OpenAI matrix with rows indexed by $O$ and columns indexed by the exponent vectors $e \in \mathbb{N}^{J}$ of total degree at most $\mathrm{degree}$: its $(o, e)$ entry is
--   $$\sum_{T \subseteq \mathrm{rows}(o)} (-1)^{|\mathrm{rows}(o) \setminus T|}\, v_T^{\,e}, \qquad v_T = \Bigl(x_j(\mathrm{none}) + \sum_{r \in T} D_{r,j}\Bigr)_{j \in J} \in \mathbb{Z}^{J},$$
--   where $v^{e} = \prod_{j} v_j^{e_j}$.
--
--   Lean: `OAI.Erdos3.goodKernelUniformCandidate_spec_s2`, which states OpenAI's `OAI.Erdos3.goodKernelUniformCandidate_spec` (in `lean/OAI/Combinatorics/Progressions/Linear/KernelCoefficientLogBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B099` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/KernelCoefficientLogBudget.lean (declaration OAI.Erdos3.goodKernelUniformCandidate_spec)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B099

section

namespace OAI

section

namespace Erdos3

theorem goodKernelUniformCandidate_spec_s2 {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (height : ℕ) :
    let period := kernelPeriodCandidate (height + 1) (goodKernelUniformCandidate selection x hx height)
    (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    ∀ (O : Type*) [Fintype O] (degree : ℕ), degree ≤ height + 1 →
      ∀ rows : O → Finset α, Function.Injective rows →
        (∀ o, (rows o).card ≤ degree) →
          integerScalarLattice O (period : ℤ) ≤ (scalarKernelIntegerJet x degree rows).mulVecLin.range := by
  sorry

end Erdos3

end

end OAI
end
