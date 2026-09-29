-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/3b98e64e-a1f7-5a66-838b-a04401438aab
-- title:
--   Unipotent-fixed stable subspace of a unitary principal series vanishes
-- statement:
--   Let $p$ be a height one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_p$ for the associated adic completion, and let $\theta = (\theta_0,\theta_1)$ be a pair of group homomorphisms $\mathbb{Q}_p^\times \to \mathbb{C}^\times$, indexed by `Fin 2`, subject to two conditions: all values are of complex absolute value $1$, and there are natural numbers $c_0, c_1$ such that $\theta_i$ is trivial on `higherUnitsAt ℚ p (c i)`, the set of units $u$ with $v(u) = 1$ and, when $c_i \neq 0$, $v(u-1) \le \exp(-c_i)$. The space `principalSeries2 p θ` consists of the locally constant functions $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ with $f\bigl(\binom{1\ x}{0\ 1} g\bigr) = f(g)$ for all $x \in \mathbb{Q}_p$ and $f(\mathrm{diag}(a_0,a_1)\, g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\, f(g)$ for all $a_0, a_1 \in \mathbb{Q}_p^\times$, and `principalSeries2Rep θ g` is right translation $f \mapsto (h \mapsto f(hg))$ on this space. The assertion is that a $\mathbb{C}$-submodule $V$ of this space which is stable under `principalSeries2Rep θ g` for every $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, and on which every upper unipotent $\binom{1\ x}{0\ 1}$ acts as the identity, is the zero submodule.
--
--   This is the degenerate-subrepresentation step in the irreducibility analysis of the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ attached to a pair of unitary characters: no nonzero stable subspace can be fixed pointwise by the unipotent radical. It is used in [`LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one), where a nonzero vector is shown to generate the whole space under right translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_bot_of_stable_of_forall_principalSeries2Rep_upperUnipotent2_eq_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hN : ∀ (x : p.adicCompletion ℚ), ∀ v ∈ V, principalSeries2Rep θ (upperUnipotent2 p x) v = v) :
    V = ⊥ := by sorry
