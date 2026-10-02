-- Prove2me | Theorems.Thm_LeblSCV_Germs_weierstrass_preparation
-- name    : LeblSCV.Germs.weierstrass_preparation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:47.876638+00:00
-- url     : https://prove2.me/theorems/8694c8c5-b1ed-45ba-9d5e-40f2ba466bad
-- title:
--   Theorem 6.2.3 — Weierstrass preparation theorem
-- statement:
--   Let $U \subset \mathbb{C}^{n-1} \times \mathbb{C}$ be open with $0 \in U$, and let $f \in \mathcal{O}(U)$ with $f(0) = 0$. Suppose that $z_n \mapsto f(0, z_n)$ is not identically zero near the origin and that its order of vanishing at the origin is $k \ge 1$.
--
--   Then there exist an open polydisc $V = V' \times D \subset \mathbb{C}^{n-1} \times \mathbb{C}$ with $0 \in V \subset U$, a function $u \in \mathcal{O}(V)$ with $u(z) \neq 0$ for all $z \in V$, and a Weierstrass polynomial $P(z', z_n) = z_n^k + \sum_{\ell=0}^{k-1} c_\ell(z') z_n^\ell$ of degree $k$ with coefficients holomorphic in $V'$, such that
--   $$ f(z', z_n) = u(z', z_n)\, P(z', z_n) \qquad \text{for } (z', z_n) \in V, $$
--   and such that all $k$ zeros (counting multiplicity) of $z_n \mapsto P(z', z_n)$ lie in $D$ for every $z' \in V'$. Moreover $u$ and $P$ are unique: any other pair $(u_2, P_2)$ with the same properties on this $V$ has $u_2 = u$ on $V$ and the same coefficients on $V'$.
--
--   This is the several-variable analogue of writing a one-variable holomorphic function as $z^k$ times a unit; it reduces local questions about holomorphic functions to questions about polynomials in one variable over the ring of functions of the remaining variables.
--
--   **Formalization Note.** $\mathbb{C}^{n-1} \times \mathbb{C}$ is `(Fin d → ℂ) × ℂ` with $d = n - 1$ ($d = 0$ is the case $n = 1$). Holomorphic means `DifferentiableOn ℂ` on an open set. $V' = \Delta_{\rho'}(a')$ is a polydisc with positive radii and $D$ is the open disc `Metric.ball a ρ` with $\rho > 0$; the book does not require the centers to be $0$, so neither does the statement. The hypothesis on $z_n \mapsto f(0,z_n)$ is `orderOfVanishing (fun w => f (0, w)) 0 = k`, which also excludes the identically-zero case (order $\infty$). Since $P(z', \cdot)$ is monic of degree $k$, it has exactly $k$ zeros counted with multiplicity, so "all $k$ zeros lie in $D$" is stated as "every zero lies in $D$". Uniqueness is stated among pairs satisfying all the listed properties on the same $V$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 170, Theorem 6.2.3

import Mathlib
import Definitions.Def_LeblSCV_Germs_orderOfVanishing
import Definitions.Def_LeblSCV_Germs_weierstrassPolynomial
import Definitions.Def_LeblSCV_Shared_polydisc

namespace LeblSCV.Germs

/-- Theorem 6.2.3 (Weierstrass preparation theorem, Lebl, p. 170). `ℂ^{n-1} × ℂ` is
`(Fin d → ℂ) × ℂ` with `d = n - 1` (`d = 0` is the case `n = 1`). Let `f` be holomorphic on an
open `U ∋ 0` with `f(0) = 0`, and suppose `z_n ↦ f(0, z_n)` is not identically zero near the
origin and has order of vanishing `k ≥ 1` there. Then there is an open polydisc
`V = V' × D ⊆ ℂ^{n-1} × ℂ` (`V' = Δ_{ρ'}(a')`, `D` the disc of radius `ρ` about `a`) with
`0 ∈ V ⊆ U`, a nonvanishing `u ∈ 𝒪(V)` and a Weierstrass polynomial `P` of degree `k` with
coefficients `c_ℓ` holomorphic in `V'`, such that `f = u P` on `V` and all zeros of
`z_n ↦ P(z', z_n)` lie in `D` for every `z' ∈ V'`; and `u` and `P` are unique with these
properties (as functions on `V`, resp. coefficients on `V'`). -/
theorem weierstrass_preparation {d : ℕ} (U : Set ((Fin d → ℂ) × ℂ)) (hU : IsOpen U)
    (h0U : (0 : (Fin d → ℂ) × ℂ) ∈ U) (f : (Fin d → ℂ) × ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0) (k : ℕ) (hk : 1 ≤ k)
    (hord : orderOfVanishing (fun w : ℂ => f (0, w)) 0 = (k : ℕ∞)) :
    ∃ (a' : Fin d → ℂ) (ρ' : Fin d → ℝ) (a : ℂ) (ρ : ℝ),
      (∀ j, 0 < ρ' j) ∧ 0 < ρ ∧
      (0 : (Fin d → ℂ) × ℂ) ∈ LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ ∧
      LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ ⊆ U ∧
      ∃ (u : (Fin d → ℂ) × ℂ → ℂ) (c : Fin k → (Fin d → ℂ) → ℂ),
        DifferentiableOn ℂ u (LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ) ∧
        (∀ z ∈ LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ, u z ≠ 0) ∧
        IsWeierstrassPolynomial (LeblSCV.Shared.polydisc a' ρ') c ∧
        (∀ z ∈ LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ, f z = u z * weierstrassPolyFun c z) ∧
        (∀ z' ∈ LeblSCV.Shared.polydisc a' ρ', ∀ w : ℂ, weierstrassPolyFun c (z', w) = 0 →
          w ∈ Metric.ball a ρ) ∧
        ∀ (u₂ : (Fin d → ℂ) × ℂ → ℂ) (c₂ : Fin k → (Fin d → ℂ) → ℂ),
          DifferentiableOn ℂ u₂ (LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ) →
          (∀ z ∈ LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ, u₂ z ≠ 0) →
          IsWeierstrassPolynomial (LeblSCV.Shared.polydisc a' ρ') c₂ →
          (∀ z ∈ LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ, f z = u₂ z * weierstrassPolyFun c₂ z) →
          (∀ z' ∈ LeblSCV.Shared.polydisc a' ρ', ∀ w : ℂ, weierstrassPolyFun c₂ (z', w) = 0 →
            w ∈ Metric.ball a ρ) →
          Set.EqOn u₂ u (LeblSCV.Shared.polydisc a' ρ' ×ˢ Metric.ball a ρ) ∧
            ∀ ℓ : Fin k, Set.EqOn (c₂ ℓ) (c ℓ) (LeblSCV.Shared.polydisc a' ρ') := by sorry

end LeblSCV.Germs
