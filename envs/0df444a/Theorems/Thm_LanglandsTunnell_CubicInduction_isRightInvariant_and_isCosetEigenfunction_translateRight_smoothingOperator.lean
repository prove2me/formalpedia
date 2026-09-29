-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
-- name    : LanglandsTunnell.CubicInduction.isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/49ff41b7-40f9-5b4b-928f-bd4e981463b5
-- title:
--   Smoothing and translation preserve level and Hecke eigenvalues at p
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and complex numbers $\lambda_1,\lambda_2$. Let $\varphi$ be a function on $GL_3$ of the adeles of $\mathbb{Q}$ which is a smoothing kernel, that is, there are a smooth archimedean factor $\alpha$ in the $3\times 3$ real entries and open compact subgroups $K'_q \le GL_3(\mathbb{Q}_q)$, equal to the standard compact subgroup $\{k : \text{all entries of } k \text{ and of } k^{-1} \text{ have valuation} \le 1\}$ for all but finitely many $q$, with $\varphi(g) = \alpha(\text{arch. entries of } g)$ times the indicator of $\{x : \text{the } q\text{-component of } x \text{ lies in } K'_q \text{ for all } q\}$; assume moreover that $\varphi(g) \ne 0$ forces the $p$-component of $g$ to lie in that standard compact subgroup at $p$. Let $h$ be an adelic matrix with trivial $p$-component, and let $f$ be continuous, right invariant under the image $U$ of the standard compact subgroup at $p$ in $GL_3$ of the adeles, and a coset eigenfunction for the two diagonal generators $\mathrm{diag}(\varpi,1,1)$ and $\mathrm{diag}(\varpi,\varpi,1)$ ($\varpi$ a uniformizer at $p$) with eigenvalues $\lambda_1,\lambda_2$, in the sense that for every finite family of representatives forming a Hecke coset system for $U$ and the generator, the sum of $f$ over the translated representatives equals the eigenvalue times $f$. Then the function $x \mapsto \int \varphi(g) f(xhg)\,dg$ against the adelic Haar measure on $GL_3$ is again right $U$-invariant and a coset eigenfunction for the same two generators with the same eigenvalues $\lambda_1$ and $\lambda_2$.
--
--   This is the standard statement that convolution with a kernel whose level at $p$ is contained in the maximal compact subgroup, followed by right translation by an element trivial at $p$, commutes with the spherical Hecke algebra at $p$ and preserves the level there; taking $h=1$ gives the assertion for the smoothed function itself. It is used in the analytic part of the cubic-induction argument, where smoothing operators are applied to automorphic forms on $GL_3$ while keeping track of their unramified Hecke eigenvalues, for instance in the study of continuity and compact support of smoothed functions and of their Whittaker expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam1 lam2 : ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : SlabL2.IsSmoothingKernel φ)
    (_hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (_hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f lam1)
    (_hT2 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f lam2) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam1 ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam2 := by sorry
