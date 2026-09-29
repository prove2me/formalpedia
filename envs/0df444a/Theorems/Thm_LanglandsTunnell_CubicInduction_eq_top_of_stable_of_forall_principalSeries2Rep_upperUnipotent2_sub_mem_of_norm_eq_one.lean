-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_top_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_sub_mem_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.eq_top_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_sub_mem_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/147fbe58-2b10-5387-bb49-2b641f05aa82
-- title:
--   Unipotent-cotrivial stable subspace of a principal series is everything
-- statement:
--   Let $p$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_p$ for the $p$-adic completion $\mathbb{Q}$ at $p$, and let $\theta = (\theta_0,\theta_1)$ be a pair of group homomorphisms $\mathbb{Q}_p^{\times} \to \mathbb{C}^{\times}$ indexed by `Fin 2`. Assume each $\theta_i$ is unitary, in the sense that $\lVert \theta_i(z)\rVert = 1$ for every unit $z$, and that there are natural numbers $c_0, c_1$ with $\theta_i(u) = 1$ for every $u$ in `higherUnitsAt ℚ p (c i)`, i.e. every unit $u$ with $v(u) = 1$ and, unless $c_i = 0$, also $v(u-1) \le \exp(-c_i)$. Let `principalSeries2 p θ` be the $\mathbb{C}$-subspace of functions $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ that are locally constant, satisfy $f(n(x)g) = f(g)$ for $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ and all $x \in \mathbb{Q}_p$, $g$, and satisfy $f(\mathrm{diag}(a_0,a_1)g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\, f(g)$. Let $V$ be a $\mathbb{C}$-submodule of this space which is stable under the right-translation action $(\rho(g)f)(h) = f(hg)$ of every $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, and suppose $\rho(n(x))f - f \in V$ for every $x \in \mathbb{Q}_p$ and every $f$ in the principal series. Then $V$ is the whole space.
--
--   This is the quotient half of the irreducibility argument for the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ attached to a pair of unitary characters: a translation-stable subspace whose quotient carries a trivial action of the unipotent radical must be everything. It is used in the local analysis of the principal series occurring in the Langlands–Tunnell input, in particular to show that a nonzero vector generates the whole representation under right translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_top_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_sub_mem_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_top_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_sub_mem_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hq : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V) :
    V = ⊤ := by sorry
