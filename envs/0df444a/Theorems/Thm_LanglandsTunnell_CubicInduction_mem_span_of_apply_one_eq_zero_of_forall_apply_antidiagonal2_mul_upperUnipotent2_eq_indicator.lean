-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
-- name    : LanglandsTunnell.CubicInduction.mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1ced178f-41a1-55ff-9d8d-46246d05c0c4
-- title:
--   Big-cell ball vectors span the kernel of evaluation at 1
-- statement:
--   Fix a height one prime $p$ of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_p :=$ `p.adicCompletion ℚ`, and a pair $\theta = (\theta_0,\theta_1)$ of characters, i.e. monoid homomorphisms $\mathbb{Q}_p^\times \to \mathbb{C}^\times$. Here `principalSeries2 p θ` is the $\mathbb{C}$-submodule of functions $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ that are locally constant, satisfy $f(n(x)g) = f(g)$ for all $x \in \mathbb{Q}_p$ and all $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfy $f(\mathrm{diag}(a_0,a_1)\,g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,f(g)$ for all $a_0,a_1 \in \mathbb{Q}_p^\times$ and all $g$. Let $\varphi : \mathbb{Z} \to \mathbb{Q}_p \to$ `principalSeries2 p θ` be a family of elements of this space such that, for all $n \in \mathbb{Z}$ and $t \in \mathbb{Q}_p$, one has $\varphi_{n,t}(1) = 0$ and, for all $x \in \mathbb{Q}_p$, $\varphi_{n,t}(w\,n(x))$ equals $1$ if $v(x-t) \le \exp(-n)$ and $0$ otherwise, where $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $v$ is the valuation of $\mathbb{Q}_p$ with values in $\mathbb{Z}^{\mathrm{mult}}$ with zero. Then every $f$ in `principalSeries2 p θ` with $f(1) = 0$ lies in the $\mathbb{C}$-span of the set of all $\varphi_{n,t}$, $(n,t) \in \mathbb{Z} \times \mathbb{Q}_p$.
--
--   This is the surjectivity half of the standard description, coming from the Bruhat decomposition of $\mathrm{GL}_2(\mathbb{Q}_p)$, of the subspace of a normalised principal series consisting of vectors supported on the big cell: such vectors are spanned by the ones whose big-cell profile is the indicator function of a ball. It is used in the proof that a vector of the principal series whose matrix coefficients against a given family all have the prescribed determinant-twisted form must vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : ℤ → p.adicCompletion ℚ → ↥(principalSeries2 p θ))
    (hφ1 : ∀ (n : ℤ) (t : p.adicCompletion ℚ), (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0)
    (hφ : ∀ (n : ℤ) (t x : p.adicCompletion ℚ),
      (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
        if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)
    (f : ↥(principalSeries2 p θ)) (h1 : (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0) :
    f ∈ Submodule.span ℂ (Set.range fun nt : ℤ × p.adicCompletion ℚ => φ nt.1 nt.2) := by sorry
