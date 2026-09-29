-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
-- name    : LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5e70542e-b376-5891-9996-66fd1d3286ab
-- title:
--   Unipotent radical acts trivially modulo a translation-stable subspace
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, let $\theta_0,\theta_1$ be homomorphisms from the units of the completion $\mathbb{Q}_p$ to $\mathbb{C}^\times$, and let $c_0,c_1$ be natural numbers such that each $\theta_i$ is trivial on the set of units $u$ with $|u|=1$ satisfying $c_i = 0$ or $v(u-1)\le \exp(-c_i)$. Write $I(\theta)$ for the space of locally constant functions $f$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ that are left invariant under the matrices $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and satisfy $f(\mathrm{diag}(a_0,a_1)g)=\theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$, with $\mathrm{GL}_2(\mathbb{Q}_p)$ acting by right translation. Let $V\subseteq I(\theta)$ be a $\mathbb{C}$-subspace stable under right translation by every $g\in \mathrm{GL}_2(\mathbb{Q}_p)$. Assume that for every additive character $\psi'$ of $\mathbb{Q}_p$ which is trivial on some ball $\{y : v(y)\le\exp k\}$, $k\in\mathbb{Z}$, and is not the trivial character, every $\mathbb{C}$-linear functional $L$ on $I(\theta)$ with $L(n(x)\cdot f)=\psi'(x)L(f)$ for all $x$ and $f$, and vanishing identically on $V$, is zero. Then for every $x\in\mathbb{Q}_p$ and every $f\in I(\theta)$ one has $n(x)\cdot f - f\in V$.
--
--   This is the quotient form of the Whittaker-functional criterion for the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$: absence of nonzero twisted Whittaker functionals on $I(\theta)/V$ forces the unipotent radical to act trivially on that quotient, the statement being phrased without forming the quotient module. It feeds the analysis of translation-stable subspaces of the principal series, being cited by `mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hdeg : ∀ (ψ' : AddChar (p.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (L : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ),
        (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)),
          L (principalSeries2Rep θ (upperUnipotent2 p x) f) = ψ' x * L f) → (∀ v ∈ V, L v = 0) → L = 0)
    (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)) :
    principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V := by sorry
