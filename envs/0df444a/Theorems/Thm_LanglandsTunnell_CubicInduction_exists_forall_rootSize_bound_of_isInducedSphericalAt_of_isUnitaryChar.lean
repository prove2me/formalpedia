-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
-- name    : LanglandsTunnell.CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5f41602f-2189-5f26-a875-c46a2d5aa1d3
-- title:
--   Uniform root-size bound for induced spherical Whittaker functions
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a homomorphism with $\|\mu(x)\| = 1$ for all $x$, and let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$. The assertion is that there is an exponent $t \in \mathbb{N}$, depending only on these data, such that for every finite place $v$ of $\mathbb{Q}$ satisfying: $v$ is neither ramified in $K$ nor twist-ramified above for $\mu$ (the two disjuncts of `IsBadPlace`), the local character $\psi_v =$ `psiLoc` $\psi\,v$ is trivial on $\{x : |x|_v \le 1\}$, and $\psi_v$ is non-trivial at $\varpi_v^{-1}x$ for some such $x$; and for every $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ with $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for all upper unipotent $u(x,y,z)$ and all $g$, which is right invariant under the subgroup of matrices whose entries and whose inverse's entries all have valuation $\le 1$, is a coset eigenfunction for the two Hecke generators with eigenvalues `cNormQ` $v$ times the first and second induced coefficients of $\mathfrak{P} \mapsto \mu(\text{uniformizer idele at }\mathfrak{P})$ (taken to be $0$ where $\mu$ ramifies) and satisfies $W(\text{centralGen}\,v\cdot g) = e_3 \, W(g)$, with $W(1) = 1$ and the prescribed `HasSphericalTorusValuesAt` values on the torus points $\iota(n)$ and the two-row points $(k_1,k_2+1)$, $k_2+1 \le k_1$: writing $d = \|\det h\|$, $r$ for the maximum of the norms of the last-row entries, $m$ for the maximum of the norms of the three $2\times 2$ minors of the bottom two rows, and $A = dr/m^2$, $B = m/r^2$, one has $W(h) = 0$ whenever not both $A \le 1$ and $B \le 1$, and $\|W(h)\| \le 1/(AB)^t$ whenever $A \le 1$ and $B \le 1$.
--
--   This is the uniform local majorant, in terms of the two root sizes of the mirabolic decomposition, for the spherical Whittaker functions attached at the good primes to the automorphic induction of a unitary character of a cubic field. It supplies the growth bound used when the local data at a place are assembled into the cubic induction package, and is cited by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_forall_rootSize_bound_of_isInducedSphericalAt_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) :
    ∃ t : ℕ, ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ¬ IsBadPlace K μ v →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1) →
      (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) →
      ∀ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W →
      ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖W h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by sorry
