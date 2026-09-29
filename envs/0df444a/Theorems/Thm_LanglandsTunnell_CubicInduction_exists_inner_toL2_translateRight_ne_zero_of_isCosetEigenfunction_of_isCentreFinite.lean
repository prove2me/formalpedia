-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite
-- name    : LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6bf5f5b3-9e2b-5370-a6c8-ede38dbc6d8a
-- title:
--   Hecke-matched GL₃ cusp forms non-orthogonal after right translation
-- statement:
--   Fix a finite set $S$ of nonzero primes of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $\|\omega(z)\|=1$ for all $z$, functions $\lambda_1,\lambda_2$ from primes to $\mathbb{C}$, reals $a<b$ with $0<a$, and a set $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ that is a fundamental domain for the image of the rational points with respect to the slab measure. Let $F$ and $F'$ both be cusp functions for $(\omega,a,b,\Phi_0)$, i.e. continuous, invariant under left translation by rational points, transforming by $\omega$ under adelic central scalars, square-integrable for the domain measure attached to $(a,b,\Phi_0)$, and cuspidal along the two directions $P_{21}$ and $P_{12}$ for the standard pin datum; assume each has nonzero $L^2$ class, is invariant under right translation by the image in the adelic group of the local maximal compact subgroup $\{k:\ v(k_{ij})\le 1,\ v((k^{-1})_{ij})\le 1\}$ at every $p\notin S$, and is, at every $p\notin S$, a coset eigenfunction with eigenvalue $\lambda_1(p)$ for $\mathrm{diag}(\varpi_p,1,1)$ and $\lambda_2(p)$ for $\mathrm{diag}(\varpi_p,\varpi_p,1)$, in the sense that for every finite system of Hecke coset representatives the associated coset sum is the eigenvalue times the function. Assume furthermore that for every smoothing kernel $\varphi$ (a smooth archimedean factor times the indicator of a product of open compact subgroups, almost all maximal) for which $\varphi*F=\int \varphi(g)F(\,\cdot\,g)\,dg$ is again a cusp function and is archimedean-smooth, $\varphi*F$ is centre-finite, i.e. each of the three Casimir operators annihilates it after application of a monic polynomial. Then there exists $g\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that $x\mapsto F(xg)$ again lies in the automorphic submodule and its $L^2$ class has nonzero inner product with the $L^2$ class of $F'$.
--
--   This is the non-orthogonality (rigidity) step for $\mathrm{GL}_3$ in the style of Jacquet–Shalika: two cusp functions with the same spherical Hecke eigenvalues outside a finite set cannot have all right translates of one orthogonal to the other. The present version carries a centre-finiteness hypothesis on the smoothings of $F$ as an assumption rather than deriving it, and it is cited by [`LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction`](thm.html#LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction), where that hypothesis is discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

theorem
LanglandsTunnell.CubicInduction.exists_inner_toL2_translateRight_ne_zero_of_isCosetEigenfunction_of_isCentreFinite
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (_hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p))
    (_hcf : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
      smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀ → WhittakerBlock.IsArchSmooth3 (smoothingOperator φ F) →
        WhittakerBlock.IsCentreFinite (smoothingOperator φ F))
    (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀) (_hF'0 : toL2 ω a b Φ₀ ⟨F', hF'.1⟩ ≠ 0)
    (_hK' : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F')
    (_hT1' : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F' (lam1 p))
    (_hT2' : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F' (lam2 p)) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ ≠ 0 := by sorry
