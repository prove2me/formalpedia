-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_mesh_truncation_bound_s2
-- name    : OAI.Erdos3.affine_mesh_truncation_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:48:30.838106+00:00
-- url     : https://prove2.me/theorems/a630d9e2-6ec1-46eb-b4f1-610193a119ab
-- title:
--   A bound for the weighted mean of physical box truncations along smooth affine samples, via cell-wise truncated pairings and a mesh-crossing probability
-- statement:
--   Let $\iota, I, J$ be finite types ($\iota$ with decidable equality). A `FiniteProgressionPartition N` (a structure defined by OpenAI) is a partition of $\{0, \dots, N-1\}$ into finitely many arithmetic progressions, indexed by a finite type of labels, each label $c$ having a start, a step and a length. For a box $\prod_i [\ell_i, \ell_i + N_i)$ and partitions $P_i$ of $[0, N_i)$, a product label $c = (c_i)$ determines the cell box with lower corner $(\ell_i + \mathrm{start}(c_i))_i$ (`intervalCellLower`) and side lengths $(\mathrm{length}(c_i))_i$. For such a cell, a vector of positive moduli $q : \iota \to \mathbb{N}$ and a function $f$ on integer points, write $\rho_{c}[f]$ for `residuePrimeCoordinateDensity` of the cell (with modulus $1$, offset $0$), $q$ and $f$: this is the function on $\prod_{k \in \iota} (\mathbb{Z}/q_k)^{I}$ (or the analogous product with index set $\mathrm{Option}\,J \times I$ or $J$) equal to the density, with respect to the uniform law, of the reduction modulo $q$ of a uniform point $x$ of the cell, weighted by $f(x)$ (defined by OpenAI via `observedProductDensity`).
--
--   **Data and hypotheses.**
--   - $\ell : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$, and for each $i$ a partition $P_i$ of $[0, N_i)$ into progressions of step $1$ and positive length;
--   - $\mathrm{sourceLo} < \mathrm{sourceHi}$ (pointwise) as functions $\mathrm{Option}\,J \times I \to \mathbb{Z}$, and for each index $i$ a partition $S_i$ of $[0, \mathrm{sourceHi}_i - \mathrm{sourceLo}_i)$ into progressions of step $1$ and positive length;
--   - $\mathrm{paramLo} < \mathrm{paramHi}$ (pointwise) as functions $J \to \mathbb{Z}$, and for each $j$ a partition $T_j$ of $[0, \mathrm{paramHi}_j - \mathrm{paramLo}_j)$ into progressions of step $1$ and positive length;
--   - $D, b \in \mathbb{N}$, $a : J \to \mathbb{Z}$, $q : \iota \to \mathbb{N}$ with all $q_k \ne 0$;
--   - $w : \mathbb{Z}^{\mathrm{Option}\,J \times I} \to \mathbb{R}$ with $0 \le w \le 1$ on the source box $\prod [\mathrm{sourceLo}, \mathrm{sourceHi})$, and $h, g : \mathbb{Z}^I \to \mathbb{R}$ with $0 \le h, g \le 1$ on the box $\prod_i [\ell_i, \ell_i + N_i)$ (`translatedIntegerBox ℓ N`);
--   - reals $\eta_{\mathrm{param}}, \eta_{\mathrm{site}}, r, R, \beta$ with $\eta_{\mathrm{param}}, \eta_{\mathrm{site}}, r, R \ge 0$;
--   - (parameter marginals) for every product label $c_t$ of the $T_j$, `ProductMarginalsClose` holds for the uniform reference laws on $(\mathbb{Z}/q_k)^J$, the density $\rho_{c_t}[1]$ of that parameter cell, accuracy $\eta_{\mathrm{param}}$ and order $b$; `ProductMarginalsClose μ ρ η s` (defined by OpenAI) means that for every set $B$ of at most $s$ indices $k$ and every point $x$ of positive weight, the conditional mean of $\rho$ given the coordinates in $B$ is within $\eta$ of $1$;
--   - (site marginals) for every product label $c$ of the $P_i$, `ProductMarginalsClose` holds for the uniform laws on $(\mathbb{Z}/q_k)^I$, the density $\rho_c[1]$ of that site cell, accuracy $\eta_{\mathrm{site}}$ and order $b$;
--   - (reference pairings) for every product label $c_s$ of the $S_i$ and every product label $c$ of the $P_i$:
--   $$\texttt{productTruncatedPairing}\ (\texttt{affinePeriodProductCoupling}\ q\ D\ a)\ \mathcal{D}_b\ \bigl(\rho_{c_s}[w]\bigr)\ \bigl(\rho_c[h] - r\,\rho_c[g]\bigr) \le R,$$
--   where $\mathcal{D}_b$ = `lowDegreeCoordinateSets ι b` is the family of subsets of $\iota$ of size at most $b$, `affinePeriodProductCoupling q D a` is a coupling (defined by OpenAI) between the uniform laws on $(\mathbb{Z}/q_k)^{\mathrm{Option}\,J \times I}$ and on $(\mathbb{Z}/q_k)^I$, and `productTruncatedPairing c D u f` is the pairing under the coupling $c$ of the ANOVA truncations of $u$ and $f$ to the coordinate sets in $D$ (defined by OpenAI);
--   - (mesh crossing) under the product of the uniform laws on the parameter box $\prod_j [\mathrm{paramLo}_j, \mathrm{paramHi}_j)$ and the source box, the probability of `physicalMeshCrossing` is at most $\beta$; here, for a pair $(t, z)$ (parameter $t$, source point $z$), the mesh is the pair of cells of $z$ and of $t$ in the partitions $S$ and $T$ (`integerBoxMesh`), the location is the smooth affine sample $\mathrm{sas}(t, z) = \bigl(z_{(\mathrm{none}, i)} + \sum_j (a_j + D\, t_j)\, z_{(\mathrm{some}\ j, i)}\bigr)_{i \in I}$ (`smoothAffineSample`), and a crossing occurs at $(t, z)$ if some $(t', z')$ in the same mesh cell has its location classified differently from that of $(t, z)$ by `physicalBoxClassify ℓ N P` (defined by OpenAI; it records which cell of the partition $P$ of the physical box contains a point, and is `none` outside the box).
--
--   **Conclusion.** With $(t, z)$ uniform on the parameter box times the source box,
--   $$\mathbb{E}\Bigl[ w(z) \bigl( \Theta_h(\mathrm{sas}(t, z)) - r\, \Theta_g(\mathrm{sas}(t, z)) \bigr) \Bigr] \le R + (1 + r)(\eta_{\mathrm{param}} + \beta) \cdot \texttt{residueTruncationCap}\ \iota\ b\ \eta_{\mathrm{site}},$$
--   where $\Theta_f$ = `physicalBoxTruncation ℓ N P _ q b f` (defined by OpenAI) is $0$ outside the physical box and, at a point $x$ of the box, is the residue truncation of order $b$ (with moduli $q$) of $f$ on the cell of $P$ containing $x$, evaluated at $x$; and `residueTruncationCap ι b η` $= |\mathcal{D}_b| \cdot 2^b \cdot (1 + \eta)$.
--
--   Lean: `OAI.Erdos3.affine_mesh_truncation_bound_s2`, which states OpenAI's `OAI.Erdos3.affine_mesh_truncation_bound` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshScalarTail.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshScalarTail.lean (declaration OAI.Erdos3.affine_mesh_truncation_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_truncation_bound_s2
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ i, sourceLo i < sourceHi i)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ)
    (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hcloseParam : ∀ ct : (∀ j, (T j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) q)
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (T j) (ct j))
          (fun j => (T j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) T hTpos ct)
          q (fun _ => 1)) etaParam b)
    (hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) q)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          q (fun _ => 1)) etaSite b)
    (hreference : ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
      productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
          (fun i => (S i).length (cs i)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs) q w)
        (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q h x -
          r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
            (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c) q g x) ≤ R)
    (hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta) :
    ((integerBoxUniformWeights paramLo paramHi hparam).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) *
        (physicalBoxTruncation lo N P hPpos q b h
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) -
          r * physicalBoxTruncation lo N P hPpos q b g
            (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))) ≤
      R + (1 + r) * (etaParam + beta) * residueTruncationCap ι b etaSite := by
  sorry

end Erdos3

end

end OAI
end
