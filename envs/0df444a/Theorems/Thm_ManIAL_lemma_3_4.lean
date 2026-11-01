-- Prove2me | Theorems.Thm_ManIAL_lemma_3_4
-- name    : ManIAL.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:14.609612+00:00
-- url     : https://prove2.me/theorems/2a6419f0-9565-42a9-90bb-6c64880f50ea
-- title:
--   Lemma 3.4 — inner RGD calls for Options I and II (corrected: factor 2 restored from Lemma 3.2)
-- statement:
--   Suppose Assumption 1 holds (as in Lemma 3.3). Let $\sigma_k>0$, $z^k\in\mathbb R^m$, $\psi_k=\mathcal L_{\sigma_k}(\cdot,z^k)$, let $G>0$ bound $\|\nabla\psi_k\|$ on $\mathcal M$, $L_k=\alpha^2(\ell_{\nabla f}+\sigma_k\|\mathcal A\|^2)+2G\beta$, $x^k\in\mathcal M$, let $m\le\psi_k$ on $\mathcal M$, $\epsilon_k>0$, and put $\Delta_k=\psi_k(x^k)-m$. Let $u_t$ be the iterates of RGD on $\psi_k$ with stepsize $1/L_k$ from $u_0=x^k$.
--
--   1. **Option I.** For every integer $T_k\ge\max\big(1,\,2L_k\Delta_k/\epsilon_k^2\big)$, every output $x^{k+1}=u_{t^*}$ of $\mathrm{RGD}(\psi_k,L_k,T_k,x^k)$ satisfies (3.12): $\|\operatorname{grad}\psi_k(x^{k+1})\|\le\epsilon_k$.
--   2. **Option II.** Every output $x^{k+1}=u_{t^*}$ of $\mathrm{RGD}(\psi_k,L_k,2^k,x^k)$ satisfies
--   $$
--   \|\operatorname{grad}\psi_k(x^{k+1})\|\le\frac{\sqrt{2L_k\Delta_k}}{\sqrt{2^k}} .
--   $$
--
--   Here an output is $u_{t^*}$ with $t^*\in\arg\min_{0\le t\le T}\|\operatorname{grad}\psi_k(u_t)\|$. These are the inner complexities that Theorem 3.8 sums over the outer iterations.
--
--   Differences from the source:
--   - correction: T_k = L_k(ψ_k(x^k) − ψ_{k,min})/ϵ_k² and (3.25) ‖grad ψ_k(x^{k+1})‖ ≤ √(L_k(ψ_k(x^k) − ψ_{k,min}))/√(2^k) → T_k ≥ max(1, 2L_kΔ_k/ϵ_k²) and ‖grad ψ_k(x^{k+1})‖ ≤ √(2L_kΔ_k)/√(2^k); reason: the printed lemma drops the factor 2 of Lemma 3.2 and is false: on a circle of large radius with the exponential retraction, a ψ whose derivative along the arc is a triangle wave between g/2 and g (slopes ±L, period g/L) followed by a ramp to 0 is retr-smooth with L, every RGD iterate has ‖grad ψ‖ = g, and Δ = T·3g²/(4L) + g²/(2L), so √(LΔ/T) < g for T ≥ 3 (at T = 4: 0.935g); Option I with ϵ_k ∈ (√3g/2, g) fails after T_k steps
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ with a retraction R → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, R any map with R_x(T_xM) ⊆ M and the bounds (2.1) for some α, β > 0; reason: §3 uses (M, R) only through these properties; Proposition 2.2 gives them for every retraction on a compact submanifold, so the paper's setting is a special case
--   - generalization: (x^k, y^k, z^k) the k-th iterate of Algorithm 1; ψ_{k,min} = inf_M ψ_k → any σ_k > 0, z^k, x^k ∈ M; any lower bound m of ψ_k on M; reason: contains every iterate; m = ψ_{k,min} gives the printed quantity
--   - reading: we can find x^{k+1} by the call RGD(ψ_k, L_k, T_k, x^k), T_k real → every integer T_k ≥ max(1, bound) and every argmin output; reason: Algorithm 2 takes an integer T > 0 and outputs an argmin
--   - reading: G of Lemma 3.3 → G > 0; reason: the proof of Lemma 3.3 chooses G > 0; it makes L_k > 0 as Algorithm 2 requires
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Lemma 3.4, displays (3.23)–(3.25), p.11

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ManIAL_RetrBounds
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_Lk
import Definitions.Def_ManIAL_rgdSeq

open ZORiem.RGD

namespace ManIAL

/-- **Lemma 3.4** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.11), corrected by the factor 2 of
Lemma 3.2. Under Assumption 1, let `σ_k > 0`, `z^k ∈ ℝᵐ`, `ψ_k = 𝓛_{σ_k}(·, z^k)`, let `G > 0`
bound `‖∇ψ_k‖` on `M`, `L_k = α²(ℓ_{∇f} + σ_k‖A‖²) + 2Gβ`, `x^k ∈ M`, let `m ≤ ψ_k` on `M`, and
`ϵ_k > 0`. Write `Δ_k = ψ_k(x^k) − m`.
* **Option I:** for every integer `T_k ≥ max(1, 2L_kΔ_k/ϵ_k²)`, every output `x^{k+1}` of
  `RGD(ψ_k, L_k, T_k, x^k)` satisfies (3.12), `‖grad ψ_k(x^{k+1})‖ ≤ ϵ_k`.
* **Option II:** every output `x^{k+1}` of `RGD(ψ_k, L_k, 2^k, x^k)` satisfies
  `‖grad ψ_k(x^{k+1})‖ ≤ √(2L_kΔ_k) / √(2^k)`.

**Formalization Note.** An output of `RGD(ψ, L, T, x)` is an iterate `u_{t*}` with
`t* ∈ argmin_{0 ≤ t ≤ T} ‖grad ψ(u_t)‖`; every tie-break is covered. The printed lemma has
`T_k = L_kΔ_k/ϵ_k²` and `√(L_kΔ_k)/√(2^k)`, which drop the factor 2 of Lemma 3.2 and are false.
`ψ_{k,min}` is replaced by any lower bound `m`. The step is stated for arbitrary `σ_k`, `z^k`,
`x^k ∈ M` rather than for the `k`-th iterate of Algorithm 1. -/
theorem lemma_3_4 {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsCompact M)
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hR : RetrBounds M R α β)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (k : ℕ) (σk : ℝ) (hσk : 0 < σk) (zk : EuclideanSpace ℝ (Fin m))
    (G : ℝ) (hG : 0 < G) (hGb : ∀ x ∈ M, ‖gradient (psi f h A σk zk) x‖ ≤ G)
    (xk : EuclideanSpace ℝ (Fin n)) (hxk : xk ∈ M)
    (mψ : ℝ) (hm : ∀ x ∈ M, mψ ≤ psi f h A σk zk x) (εk : ℝ) (hεk : 0 < εk) :
    (∀ T : ℕ, 1 ≤ T →
      2 * Lk α β G ℓf A σk * (psi f h A σk zk xk - mψ) / εk ^ 2 ≤ T →
      ∀ tstar ≤ T,
        (∀ s ≤ T, ‖rgrad M (psi f h A σk zk)
            (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk tstar)‖ ≤
          ‖rgrad M (psi f h A σk zk)
            (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk s)‖) →
        ‖rgrad M (psi f h A σk zk)
          (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk tstar)‖ ≤ εk) ∧
    (∀ tstar ≤ 2 ^ k,
        (∀ s ≤ 2 ^ k, ‖rgrad M (psi f h A σk zk)
            (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk tstar)‖ ≤
          ‖rgrad M (psi f h A σk zk)
            (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk s)‖) →
        ‖rgrad M (psi f h A σk zk)
          (rgdSeq M R (psi f h A σk zk) (Lk α β G ℓf A σk) xk tstar)‖ ≤
          Real.sqrt (2 * Lk α β G ℓf A σk * (psi f h A σk zk xk - mψ)) /
            Real.sqrt ((2 : ℝ) ^ k)) := by sorry

end ManIAL
