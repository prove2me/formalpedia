-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_mesh_scalar_tail
-- name    : OAI.Erdos3.affine_mesh_scalar_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:10:38.478698+00:00
-- url     : https://prove2.me/theorems/d3d6abad-959d-414e-b5da-2658ba27a299
-- title:
--   Small residual pairings give a tail bound for averages along random affine samples
-- statement:
--   Let $\iota$, $I$, $J$ be finite types, $\iota$ with decidable equality. A `FiniteProgressionPartition n` is OpenAI's structure bundling a finite label type and, for each label, a start, a positive step and a length, together with an identification of the disjoint union of the progressions $\{\mathrm{start} + \mathrm{step}\cdot j : j < \mathrm{length}\}$ with $\{0, \dots, n-1\}$; below every partition has all steps $1$ and all lengths positive, so that a tuple of labels names a subbox (a "cell") of the corresponding box, with lower corner shifted by the starts (`intervalCellLower`) and side lengths the lengths. A `FiniteProbabilityWeights Ω` is OpenAI's structure bundling a probability weight function on a finite type, with `mean` and `eventProbability` the associated expectation and probability. The data are:
--
--   - the site box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_i < N_i\} \subseteq \mathbb{Z}^I$, for $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$, with partitions $P_i$ of $\{0, \dots, N_i - 1\}$;
--   - the source box $\prod_{k} [\mathrm{sourceLo}_k, \mathrm{sourceHi}_k)$ indexed by $k \in \mathrm{Option}\,J \times I$, with $\mathrm{sourceLo}_k < \mathrm{sourceHi}_k$ and partitions $S_k$ of $\{0, \dots, \mathrm{sourceHi}_k - \mathrm{sourceLo}_k - 1\}$;
--   - the parameter box $\prod_{j \in J} [\mathrm{paramLo}_j, \mathrm{paramHi}_j)$ with $\mathrm{paramLo}_j < \mathrm{paramHi}_j$ and partitions $T_j$;
--   - $D \in \mathbb{N}$, $a : J \to \mathbb{Z}$, $q : \iota \to \mathbb{N}$ with nonzero values, $b \in \mathbb{N}$, and $h, g : (I \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le h, g \le 1$ on the site box;
--   - reals $\eta_{\mathrm{par}}, \eta_{\mathrm{site}}, r, R \ge 0$ and $\beta, \mathrm{acc}$.
--
--   Write $\mu^{(I)}, \mu^{(J)}$ for the products of the uniform weights `primeCoordinateReference q i` on $\prod_{i \in \iota}(I \to \mathbb{Z}/q_i)$ and $\prod_{i \in \iota}(J \to \mathbb{Z}/q_i)$, and, for a cell $Q$ and a function $\phi$, $\rho_Q[\phi]$ for `residuePrimeCoordinateDensity` of $\phi$ on $Q$ with modulus $1$ and residue $0$: the function $y \mapsto \mathbb{E}_{z \in Q}[\phi(z)\, \mathbf{1}\{(z \bmod q_i)_i = y\}] / \mu(y)$. For $(t, z)$ in the parameter box times the source box, the affine sample is $\mathrm{smp}(t, z) = $ `smoothAffineSample (fun j => a j + D * t j) z`, the point $i \mapsto z(\mathrm{none}, i) + \sum_{j} (a_j + D t_j)\, z(\mathrm{some}\ j, i)$ of $\mathbb{Z}^I$. Let $\mathbb{P}$ be the product of the uniform weights on the parameter box and on the source box (`integerBoxUniformWeights`). The hypotheses are:
--
--   1. (`hcloseParam`) for every label tuple $c_t$ of the $T_j$, `ProductMarginalsClose μ^(J) ρ_{cell c_t}[1] η_par b`, and (`hcloseSite`) for every label tuple $c$ of the $P_i$, `ProductMarginalsClose μ^(I) ρ_{cell c}[1] η_site b` — OpenAI's predicate `ProductMarginalsClose μ ρ η s`: for every $B \subseteq \iota$ with $|B| \le s$ and every $x$ with $\mu(x) \neq 0$, $|\mathbb{E}_{y \sim \mu}\, \rho(x|_B, y|_{\iota \setminus B}) - 1| \le \eta$;
--   2. (`hreference`) for every $w : (\mathrm{Option}\,J \times I \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le w \le 1$ on the source box, every source cell $c_s$ and every site cell $c$,
--   `productTruncatedPairing (affinePeriodProductCoupling q D a) (lowDegreeCoordinateSets ι b)` $\rho_{c_s}[w]$ $\bigl(\rho_c[h] - r\, \rho_c[g]\bigr) \le R$; here `affinePeriodProductCoupling q D a` is OpenAI's family (over $i \in \iota$) of couplings of the uniform weights on $\mathrm{Option}\,J \times I \to \mathbb{Z}/q_i$ and on $I \to \mathbb{Z}/q_i$, `lowDegreeCoordinateSets ι b` is the family of subsets of $\iota$ of size at most $b$, and `productTruncatedPairing c D w f` is the expectation, under the product of the coupling laws, of the product of the ANOVA truncations $\sum_{S \in D}$ `productANOVA` of $w$ and of $f$;
--   3. (`hbad`) the $\mathbb{P}$-probability of `physicalMeshCrossing` is at most $\beta$: the event that some $(t', z')$ in the same pair of mesh cells as $(t, z)$ (source cell of $z$ under the $S_k$, parameter cell of $t$ under the $T_j$; `integerBoxMesh`) has $\mathrm{smp}(t', z')$ and $\mathrm{smp}(t, z)$ classified differently by `physicalBoxClassify lo N P` (the site cell containing the point, or "outside the site box");
--   4. (`heh`, `heg`) for every $w$ with $0 \le w \le 1$ on the source box, $\bigl|\mathbb{E}_{\mathbb{P}}\bigl[w(z)\, \mathrm{res}_h(\mathrm{smp}(t, z))\bigr]\bigr| \le \mathrm{acc}$ and likewise for $g$, where $\mathrm{res}_h = $ `physicalBoxResidual lo N P hPpos q b h` (on the site box, $h$ minus its cellwise low-degree prime-coordinate truncation; $0$ off the box);
--   5. reals $p$ and $\mathrm{domLog}$ and probability weights $\nu$ on the source box with $\nu(z) \le e^{\mathrm{domLog}} \cdot \mathrm{unif}(z)$ for all $z$ (`hdom`), and
--   $$R + (1 + r)\bigl((\eta_{\mathrm{par}} + \beta) \cdot \texttt{residueTruncationCap}\ \iota\ b\ \eta_{\mathrm{site}} + \mathrm{acc}\bigr) \le \tfrac12 e^{-(2p + \mathrm{domLog})},$$
--   with `residueTruncationCap ι b η` $= |\texttt{lowDegreeCoordinateSets}\ \iota\ b| \cdot 2^{b} (1 + \eta)$.
--
--   Conclusion: with $\tilde h, \tilde g$ the extensions by zero of $h, g$ off the site box (`realZeroExtendFinset`) and $t$ uniform on the parameter box,
--   $$\nu\Bigl(\Bigl\{z : e^{-p} < \mathbb{E}_t\bigl[\tilde h(\mathrm{smp}(t, z)) - r\, \tilde g(\mathrm{smp}(t, z))\bigr]\Bigr\}\Bigr) \le e^{-p}.$$
--
--   Lean: `OAI.Erdos3.affine_mesh_scalar_tail` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshScalarTail.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshScalarTail.lean#L251

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_mesh_scalar_tail
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
    (h g : (I → ℤ) → ℝ)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    {etaParam etaSite r R beta accuracy : ℝ} (hetaParam : 0 ≤ etaParam) (hetaSite : 0 ≤ etaSite)
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
    (hreference : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      ∀ cs : (∀ i, (S i).Label), ∀ c : (∀ i, (P i).Label),
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
        (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b h
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos q b g
        (smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (p dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (herror : R + (1 + r) * ((etaParam + beta) * residueTruncationCap ι b etaSite + accuracy) ≤
      Real.exp (-(2 * p + dominationLog)) / 2) :
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) h
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        r * realZeroExtendFinset (translatedIntegerBox lo N) g
          (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-p) := by
  sorry

end Erdos3
end
end OAI
