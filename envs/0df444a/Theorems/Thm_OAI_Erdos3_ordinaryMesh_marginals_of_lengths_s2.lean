-- Prove2me | Theorems.Thm_OAI_Erdos3_ordinaryMesh_marginals_of_lengths_s2
-- name    : OAI.Erdos3.ordinaryMesh_marginals_of_lengths_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:37:41.086646+00:00
-- url     : https://prove2.me/theorems/c9e500bb-c5dc-4551-9607-14f371b08f75
-- title:
--   Long cells of a progression partition have residue densities whose low-order product marginals are within eta of 1
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $\iota$ and $I$ be finite types with decidable equality. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$, and for each $i \in I$ let $P_i$ be a finite progression partition of $\{0, \ldots, N_i - 1\}$ (OpenAI's `FiniteProgressionPartition (N i)`: a finite set of labels, each label $c$ with a start, a positive step and a length, together with a bijection between the disjoint union of the progressions and $\mathrm{Fin}(N_i)$), with every length $(P_i).\mathrm{length}(c)$ positive. Let $q : \iota \to \mathbb{N}$ with all $q_i \ge 1$ and the $q_i$ pairwise coprime. Let $b$ be a natural number and $\mathrm{modLog}, \mathrm{dimLog}, \mathrm{accLog}, \mathrm{lengthLog}, \eta$ reals with $\mathrm{modLog} \ge 0$, $\eta \le 1$, $e^{-\mathrm{accLog}} \le \eta$, $q_i \le e^{\mathrm{modLog}}$ for all $i$, $|I| \le e^{\mathrm{dimLog}}$,
--   $$\mathrm{modLog}\cdot b + \mathrm{accLog} + \mathrm{dimLog} + 1 \le \mathrm{lengthLog},$$
--   and $e^{\mathrm{lengthLog}} \le (P_i).\mathrm{length}(c)$ for all $i$ and all labels $c$.
--
--   Then for every choice of labels $c = (c_i)_{i \in I}$, the following holds. Let $\rho$ = `residuePrimeCoordinateDensity lo' N' 1 0 hne q (fun _ => 1)`, where $\mathrm{lo}'_i$ = `intervalCellLower (lo i) (P i) (c i)` $= \mathrm{lo}_i + (P_i).\mathrm{start}(c_i)$ and $N'_i = (P_i).\mathrm{length}(c_i)$; that is, $\rho$ is the density, with respect to the product over $i' \in \iota$ of the uniform laws on $(\mathbb{Z}/q_{i'})^{I}$ (`primeCoordinateReference q`), of the law of the residues $(z \bmod q_{i'})_{i'}$ of a uniformly random integer array $z$ with $z_i \in [\mathrm{lo}'_i, \mathrm{lo}'_i + N'_i)$ (the residue condition mod $1$ being vacuous; `hne` is the nonemptiness of this box). Then `ProductMarginalsClose (primeCoordinateReference q) ρ η b` holds: for every finite set $S \subseteq \iota$ with $|S| \le b$ and every point $x$ (all points have positive reference weight),
--   $$\bigl|\mathbb{E}_{y}\,\rho(x_S, y_{\iota \setminus S}) - 1\bigr| \le \eta,$$
--   where $y$ is drawn from the reference product law and $(x_S, y_{\iota\setminus S})$ takes the coordinates in $S$ from $x$ and the others from $y$ (`productConditionalMean`).
--
--   Lean: `OAI.Erdos3.ordinaryMesh_marginals_of_lengths_s2`, which states OpenAI's `OAI.Erdos3.ordinaryMesh_marginals_of_lengths` (in `lean/OAI/Combinatorics/Progressions/Estimates/OrdinaryMeshMarginals.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/OrdinaryMeshMarginals.lean (declaration OAI.Erdos3.ordinaryMesh_marginals_of_lengths)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem ordinaryMesh_marginals_of_lengths_s2 {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (modLog dimLog accLog lengthLog eta : ℝ)
    (hmod : 0 ≤ modLog) (heta : eta ≤ 1) (hacc : Real.exp (-accLog) ≤ eta)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlog : modLog * (b : ℝ) + accLog + dimLog + 1 ≤ lengthLog)
    (hlength : ∀ i c, Real.exp lengthLog ≤ ((P i).length c : ℝ))
    (c : ∀ i, (P i).Label) :
    ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0)
        (physicalBoxCell_nonempty lo N P hpos c) q (fun _ => 1)) eta b := by
  sorry

end Erdos3

end

end OAI
end
