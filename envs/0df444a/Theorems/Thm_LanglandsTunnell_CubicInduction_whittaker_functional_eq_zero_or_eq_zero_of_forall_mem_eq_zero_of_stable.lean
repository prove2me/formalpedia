-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable
-- name    : LanglandsTunnell.CubicInduction.whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/7e98ed7b-d83f-5d75-8c6e-e79a3562249b
-- title:
--   Whittaker dichotomy for a stable subspace of I(θ)
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the corresponding completion. Let $\theta = (\theta_0,\theta_1)$ be a pair of characters $F^\times \to \mathbb{C}^\times$, and let $\psi$ be an additive character of $F$ with values in $\mathbb{C}$ which is not the trivial character. Let $I(\theta) =$ `principalSeries2 p θ` be the $\mathbb{C}$-subspace of functions $f : \mathrm{GL}_2(F) \to \mathbb{C}$ that are locally constant, satisfy $f(n(x)g) = f(g)$ for the upper unipotent matrices $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfy $f(\mathrm{diag}(a_0,a_1)g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\, f(g)$ for $a_0,a_1 \in F^\times$; the group acts by right translation, $(\,g\cdot f)(h) = f(hg)$. Let $V \subseteq I(\theta)$ be a $\mathbb{C}$-subspace assumed stable under right translation by every element of $\mathrm{GL}_2(F)$. The conclusion is a disjunction: either every $\mathbb{C}$-linear functional $\ell$ on $V$ satisfying $\ell(n(x)\cdot v) = \psi(x)\,\ell(v)$ for all $x \in F$, $v \in V$ is zero; or every $\mathbb{C}$-linear functional $L$ on $I(\theta)$ satisfying $L(n(x)\cdot f) = \psi(x)\,L(f)$ for all $x \in F$, $f \in I(\theta)$ and vanishing on $V$ is zero. The proof uses the stability hypothesis on $V$ only for the upper unipotent matrices $n(x)$.
--
--   This is the elementary consequence of uniqueness of Whittaker functionals on the principal series: in the exact sequence relating $\psi$-Whittaker functionals on $I(\theta)$, on $V$ and on $I(\theta)/V$, a one-dimensional middle term forces one of the outer terms to vanish. It is used as the first step in the proof that a nonzero vector of norm one generates $I(\theta)$ under right translations ([`LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.mem_span_range_translate_of_mem_principalSeries2_of_ne_zero_of_norm_eq_one)), on the way to irreducibility of the unitary principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V) :
    (∀ ℓ : ↥V →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (v : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ x * ℓ v) → ℓ = 0) ∨
    (∀ L : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), L (principalSeries2Rep θ (upperUnipotent2 p x) f) = ψ x * L f) →
        (∀ v ∈ V, L v = 0) → L = 0) := by sorry
