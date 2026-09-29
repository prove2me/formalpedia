-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
-- name    : LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1b97256e-c87a-561c-a3b4-1637ef287a7e
-- title:
--   No twisted Whittaker functionals forces trivial unipotent action
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$, a pair $\theta = (\theta_0,\theta_1)$ of multiplicative characters $(\mathbb{Q}_p)^\times \to \mathbb{C}^\times$ of the units of the completion $\mathbb{Q}_p$ at $p$, and a pair of natural numbers $c = (c_0,c_1)$ such that each $\theta_i$ is trivial on the set of units $u$ with $|u| = 1$ and either $c_i = 0$ or $v(u-1) \le \exp(-c_i)$. Let $\mathrm{principalSeries2}\ p\ \theta$ be the space of locally constant functions $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ satisfying $f(n(x)g) = f(g)$ for the upper unipotent matrices $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $f(\mathrm{diag}(a_0,a_1)g) = \theta_0(a_0)\theta_1(a_1)\,(\|a_0\|/\|a_1\|)^{1/2} f(g)$, with $\mathrm{GL}_2(\mathbb{Q}_p)$ acting by right translation, $(\mathrm{principalSeries2Rep}\ \theta\ g\ f)(h) = f(hg)$. Let $V$ be a $\mathbb{C}$-subspace of this space, stable under all these right translations, and assume: for every additive character $\psi'$ of $\mathbb{Q}_p$ into $\mathbb{C}$ which is trivial on some ball $\{y : v(y) \le \exp(k)\}$, $k \in \mathbb{Z}$, and is not the trivial character, every $\mathbb{C}$-linear functional $\ell$ on $V$ with $\ell(n(x)\cdot w) = \psi'(x)\,\ell(w)$ for all $x \in \mathbb{Q}_p$ and $w \in V$ vanishes. Then for every $x \in \mathbb{Q}_p$ and every $v \in V$ one has $n(x)\cdot v = v$.
--
--   This is the step in Bernstein–Zelevinsky's analysis of smooth representations of the mirabolic subgroup which says that a subrepresentation of a principal series with no non-trivial twisted Whittaker functional has trivial action of the unipotent radical. It is used in the study of the translates of a vector of $\mathrm{principalSeries2}$, in particular by [`LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hdeg : ∀ (ψ' : AddChar (p.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (ℓ : ↥V →ₗ[ℂ] ℂ),
        (∀ (x : p.adicCompletion ℚ) (v : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ' x * ℓ v) → ℓ = 0)
    (x : p.adicCompletion ℚ) (v : ↥(principalSeries2 p θ)) (hv : v ∈ V) :
    principalSeries2Rep θ (upperUnipotent2 p x) v = v := by sorry
