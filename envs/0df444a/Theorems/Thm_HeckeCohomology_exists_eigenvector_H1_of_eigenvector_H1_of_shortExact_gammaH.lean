-- Prove2me | Theorems.Thm_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
-- name    : HeckeCohomology.exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/dc06bc87-f453-5aae-8e80-33606c7b9533
-- title:
--   Pulling back Hecke eigenvectors in H¹ along a short exact sequence at level Γ_H(N)
-- statement:
--   Let $N \ge 1$ and $r$ be natural numbers with $r \mid N$ and $4 \le r$, and let $H \le (\mathbb{Z}/N)^\times$ be a subgroup all of whose elements reduce to $1$ in $\mathbb{Z}/r$. Write $\Gamma =$ [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) for the subgroup of $SL_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(N)$, of the preimage of $H$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ recording the lower right entry modulo $N$. Let $\kappa$ be a field and let $X$ be a short complex $X_1 \to X_2 \to X_3$ of $\kappa$-linear representations of $\Gamma$ which is short exact, with $X_2$ finite-dimensional over $\kappa$. Let $\iota$ be an index type and, for each $i \in \iota$, let $S_1(i), S_2(i) \le \Gamma$ be subgroups with $S_2(i)$ of finite index, and $c_i : S_2(i) \to S_1(i)$ a homomorphism. For each $i$ let $\varphi_2(i)$ be a $\kappa$-linear endomorphism of $X_2$ which is a twist for these data, i.e. $\varphi_2(i)(\rho(c_i s)a) = \rho(s)(\varphi_2(i)a)$ for all $s \in S_2(i)$ and $a \in X_2$, and likewise $\varphi_3(i)$ on $X_3$; assume the map $g : X_2 \to X_3$ of the complex satisfies $g(\varphi_2(i)b) = \varphi_3(i)(g\,b)$ for all $i$ and $b$. Let `heckeH1` denote the induced endomorphisms of $H^1(\Gamma, X_2)$ and $H^1(\Gamma, X_3)$, obtained from the twisted transfer map on $1$-cocycles, and assume the operators on $H^1(\Gamma, X_2)$ commute pairwise. Let $\lambda : \iota \to \kappa$. If there is a nonzero $y \in H^1(\Gamma, X_3)$ with `heckeH1` for $\varphi_3(i)$ sending $y$ to $\lambda_i \cdot y$ for every $i$, then there is a nonzero $x \in H^1(\Gamma, X_2)$ with `heckeH1` for $\varphi_2(i)$ sending $x$ to $\lambda_i \cdot x$ for every $i$.
--
--   This is the characteristic-free lifting of a system of Hecke eigenvalues from the cohomology of a quotient coefficient module to that of the ambient one, at a level where the second cohomology of $\Gamma_H(N)$ vanishes ([`CohCarrier.subsingleton_H2_GammaH`](thm.html#CohCarrier.subsingleton_H2_GammaH)), so that $H^1(\Gamma, X_2) \to H^1(\Gamma, X_3)$ is surjective, and equivariant for the transfer Hecke operators by [`HeckeCohomology.heckeH1_natural`](thm.html#HeckeCohomology.heckeH1_natural). It feeds the analysis of eigensystems on $H^1$ with Steinberg-type quotient coefficients, via [`CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le`](thm.html#CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeCohomology.exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
    (N r : ℕ) [NeZero N] (hrN : r ∣ N) (hr : 4 ≤ r) (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ u ∈ H, ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    {κ : Type} [Field κ]
    {X : CategoryTheory.ShortComplex (Rep κ ↥(CohCarrier.GammaH N H))} (hX : X.ShortExact)
    [Module.Finite κ X.X₂]
    {ι : Type} (S₁ S₂ : ι → Subgroup ↥(CohCarrier.GammaH N H)) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i))
    [∀ i, (S₂ i).FiniteIndex]
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (hcomm : ∀ i j : ι,
      Commute (HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i))
        (HeckeCohomology.heckeH1 (S₁ j) (S₂ j) (c j) X.X₂ (φ₂ j) (hφ₂ j)))
    (lam : ι → κ)
    (hocc : ∃ y : groupCohomology.H1 X.X₃, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) y = lam i • y) :
    ∃ x : groupCohomology.H1 X.X₂, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) x = lam i • x := by sorry
