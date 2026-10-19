-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarCubeResidueWeights_riemann_s2
-- name    : OAI.Erdos3.scalarCubeResidueWeights_riemann_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:11.634578+00:00
-- url     : https://prove2.me/theorems/42da983a-d859-4ced-82cd-6eafe3130b04
-- title:
--   A Riemann-sum estimate for residue-conditioned integer scalar cube laws against Lipschitz test functions
-- statement:
--   Let $I$ be a finite type with decidable equality. Let $L, M$ be natural numbers with $L > 0$, let $m : \mathrm{Option}\,I \to \mathbb{N}$ with $0 < m_i \le M$ for all $i$, and residues $r_i \in \mathbb{Z}/m_i$. Assume $(|I| + 1) M \le L$ and
--   $$\texttt{scalarCubeGridBoundaryConstant}\ I \cdot \frac{M}{L} < \operatorname{vol}(\texttt{scalarCubeDomain}\ I),$$
--   where `scalarCubeGridBoundaryConstant I` $= 2^{|I|+1} \cdot 4^{|I|} \cdot 2 \cdot (|I| + 1)$ and `scalarCubeDomain I` $\subseteq \mathbb{R}^{\mathrm{Option}\,I}$ is the scalar cube domain, the set of $x$ such that all the cube values $x_{\mathrm{none}} + \sum_{i \in t} x_{\mathrm{some}\, i}$, $t \subseteq I$ (`scalarCubeValue`), lie in $(0, 1)$ (both defined by OpenAI). Let $\varphi : \mathbb{R}^{\mathrm{Option}\,I} \to \mathbb{R}$ be $K$-Lipschitz (sup norm; $K \ge 0$) with $|\varphi(x)| \le B$ for all $x$, where $B \ge 0$. Let $\pi$ = `scalarCubeResidueWeights I L M hL m r …` (defined by OpenAI): the law of a uniform point $z$ of the integer scalar cube set in $[-L, L)^{\mathrm{Option}\,I}$ (the integer points $z$ all of whose cube values $z_{\mathrm{none}} + \sum_{i \in t} z_{\mathrm{some}\, i}$, $t \subseteq I$, lie in $[0, L)$) conditioned on $z_i \equiv r_i \pmod{m_i}$ for all $i$. Let $\nu$ = `scalarCubeMeasure I`, the normalized Lebesgue measure on `scalarCubeDomain I`. Then
--   $$\Bigl| \mathbb{E}_{z \sim \pi}\, \varphi(z / L) - \int \varphi\, d\nu \Bigr| \le \Bigl( \frac{2B \cdot \texttt{scalarCubeGridBoundaryConstant}\ I}{\operatorname{vol}(\texttt{scalarCubeDomain}\ I)} + K \Bigr) \frac{M}{L}.$$
--
--   Lean: `OAI.Erdos3.scalarCubeResidueWeights_riemann_s2`, which states OpenAI's `OAI.Erdos3.scalarCubeResidueWeights_riemann` (in `lean/OAI/Combinatorics/Progressions/Lattices/ScalarResidueInteriorCell.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B061`, `OAIE3v2B093` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ScalarResidueInteriorCell.lean (declaration OAI.Erdos3.scalarCubeResidueWeights_riemann)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B093

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeResidueWeights_riemann_s2 (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I))
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
        (fun z => φ (fun i => (z i : ℝ) / L)) - ∫ x, φ x ∂scalarCubeMeasure I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) * ((M : ℝ)/L) := by
  sorry

end Erdos3

end

end OAI
end
