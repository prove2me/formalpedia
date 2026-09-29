-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
-- name    : LanglandsTunnell.RankinSelberg.integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/cdc47466-3745-5071-ad1c-ec3a2e041d4c
-- title:
--   Unipotent smoothing of a K₁(p^f)-invariant function on GL₃
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathcal O_{\mathbb Q}$ (a finite place of $\mathbb Q$), let $f$ be a natural number, and let $W_0 : \mathrm{GL}_3(\mathbb Q_p) \to \mathbb C$ be a function on $\mathrm{GL}_3$ of the completion $\mathbb Q_p =$ `p.adicCompletion ℚ`. Assume $W_0$ is right invariant under the set `congruenceK1 (𝓞 ℚ) ℚ p f`, that is, $W_0(gk) = W_0(g)$ for all $g$ and all $k$ such that $k$ and $k^{-1}$ have all entries of valuation $\le 1$ and the bottom row of $k$ satisfies $v(k_{2,0}) \le q^{-f}$, $v(k_{2,1}) \le q^{-f}$ and $v(k_{2,2} - 1) \le q^{-f}$ (valuations bounded by `WithZero.exp (-f)`). Let $\varphi, \varphi_1 : \mathbb Q_p \to \mathbb C$ be Schwartz–Bruhat, i.e. locally constant with compact support. Then the function
--   $$g \mapsto \int\!\!\int W_0\!\left(g \cdot \begin{pmatrix} 1 & u & y \\ 0 & 1 & 0 \\ 0 & 0 & 1\end{pmatrix}\right) \varphi(u)\,\varphi_1(y)\, dy\, du,$$
--   the iterated Bochner integral against the self-dual Haar measure `selfDualHaarAt ℚ p` on $\mathbb Q_p$ taken for the Borel $\sigma$-algebra, belongs to `gl3CyclicSubspace W₀`: the $\mathbb C$-span of the right translates $h \mapsto W_0(hg)$, $g \in \mathrm{GL}_3(\mathbb Q_p)$, of $W_0$.
--
--   This is the membership half of a local test-vector construction of Jacquet–Shalika type: smoothing a congruence-invariant function along the two-parameter unipotent subgroup $n(u,y)$ against Schwartz–Bruhat data produces only finite linear combinations of right translates. It is used in the construction of test vectors for the local Rankin–Selberg integrals, by [`LanglandsTunnell.RankinSelberg.exists_testVectors_rsLocalIntegral_eq_and_eq_const_of_centralChar_eq_of_deepTwist_of_bump`](thm.html#LanglandsTunnell.RankinSelberg.exists_testVectors_rsLocalIntegral_eq_and_eq_const_of_centralChar_eq_of_deepTwist_of_bump).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    (fun g : LocalGL3 p =>
        ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) ∈
      gl3CyclicSubspace W₀ := by sorry
