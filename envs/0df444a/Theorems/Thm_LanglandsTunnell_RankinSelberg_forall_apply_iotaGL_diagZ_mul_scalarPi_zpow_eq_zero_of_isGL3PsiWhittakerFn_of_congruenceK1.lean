-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1
-- name    : LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/26291616-a0b1-5c48-8f74-d3664571a982
-- title:
--   Vanishing of K₁-invariant GL₃ Whittaker values off the dominant cone
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$ and let $\varpi$ lie in the valuation ring of the completion $\mathbb{Q}_v$; write $\pi$ for its image in $\mathbb{Q}_v$ and assume $\pi \neq 0$ and $\mathrm{v}(\pi) = \exp(-1)$, so that $\pi$ is a uniformiser. Let $W \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the Whittaker transformation law for the inverse $\psi^{-1}$ of the standard local additive character $\psi =$ `psiLocal ℚ v`, that is, $W(u(x,y,z)\,g) = \psi^{-1}(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with $(1,2)$-entry $x$, $(2,3)$-entry $y$ and $(1,3)$-entry $z$. Let $\ell$ be a natural number and assume $W(gk) = W(g)$ for all $g$ and all $k$ in the set `congruenceK1 (𝓞 ℚ) ℚ v ℓ`, consisting of those $k \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$, and which in addition satisfy $\mathrm{v}(k_{2,0}) \le \exp(-\ell)$, $\mathrm{v}(k_{2,1}) \le \exp(-\ell)$ and $\mathrm{v}(k_{2,2} - 1) \le \exp(-\ell)$ (indices from $0$). Then for all integers $m,n$ with $n < 0$ or $m < n$ one has $W\bigl(\iota(\mathrm{diag}(\pi^{m-n},1) \cdot \mathrm{diag}(\pi,\pi)^{n})\bigr) = 0$, where $\iota$ embeds $\mathrm{GL}_2$ into $\mathrm{GL}_3$ as the upper-left block with $1$ in the remaining diagonal position; the argument is thus $\iota(\mathrm{diag}(\pi^m,\pi^n))$.
--
--   This is the standard conductor-of-$\psi$ support bound: a Whittaker function of mirabolic congruence level, restricted along the embedded $\mathrm{GL}_2$, is supported on the dominant cone $0 \le n \le m$ of torus exponents. It is used in the construction of a $K_1$-invariant vector in the cyclic $\mathrm{GL}_3$ subspace whose $\iota$-restriction is a prescribed bump function, which in turn feeds the local Rankin–Selberg zeta computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_zero_of_isGL3PsiWhittakerFn_of_congruenceK1
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ)
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (ℓ : ℕ) (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v ℓ, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∀ m n : ℤ, (n < 0 ∨ m < n) →
      W (iotaGL (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) *
        scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) = 0 := by sorry
