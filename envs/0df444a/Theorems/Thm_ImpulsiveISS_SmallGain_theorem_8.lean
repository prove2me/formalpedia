-- Prove2me | Theorems.Thm_ImpulsiveISS_SmallGain_theorem_8
-- name    : ImpulsiveISS.SmallGain.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:58:48.311455+00:00
-- url     : https://prove2.me/theorems/9bd8ca39-dbc4-4b32-b529-d53900e20184
-- title:
--   Theorem 8 (Proposition 3.1 form, flow bound off the origin) — $V=\max_i\sigma_i^{-1}(V_i(x_i))$ is an ISS-Lyapunov function of an impulsive interconnection
-- statement:
--   Consider the interconnection (4.1) of $n$ impulsive subsystems with Banach state spaces $X_i$ and input values in a Banach space $U$, written as one impulsive system (4.2) on $X=X_1\times\dots\times X_n$ with transition map $\phi_c$ of its continuous part and jump map $g=(g_1,\dots,g_n)$, and endow $X$ with the norm $\|x\|_X=\sum_i\|x_i\|_{X_i}$. Suppose:
--   1. $V_i:X_i\to\mathbb R_+$ is an ISS-Lyapunov function for the $i$-th subsystem with gains $\chi_{ij}\in\mathcal K$ ($j\ne i$), $\chi_{ii}=0$, $\chi_i\in\mathcal K$, and rates $\varphi_i,\alpha_i\in\mathcal P$, in the sense of (4.4)–(4.6);
--   2. the gain operator $\Gamma(s)_i=\max_j\chi_{ij}(s_j)$ of (4.7) satisfies the small-gain condition $\Gamma(s)\not\ge s$ for all $s\in\mathbb R^n_+\setminus\{0\}$ (4.9);
--   3. $\sigma=(\sigma_1,\dots,\sigma_n)$ is an $\Omega$-path for $\Gamma$ (Definition 5).
--
--   Let
--   $$V(x)=\max_i\sigma_i^{-1}(V_i(x_i))\quad(4.10),\qquad \chi(r)=\max_i\sigma_i^{-1}(\chi_i(r))\quad(4.11).$$
--   Then:
--   1. $V$ is continuous and there are $\psi_1,\psi_2\in\mathcal K_\infty$ with $\psi_1(\|x\|_X)\le V(x)\le\psi_2(\|x\|_X)$ for all $x\in X$ (3.1);
--   2. there is $\varphi\in\mathcal P$ such that for all $x\ne0$, $\xi\in U$ and $u\in U_c$ with $u(0)=\xi$,
--   $$V(x)\ge\chi(\|\xi\|_U)\ \Longrightarrow\ \dot V_u(x)\le-\varphi(V(x));\tag{3.5}$$
--   3. there is $\alpha\in\mathcal P$ such that for all $x\in X$, $\xi\in U$,
--   $$V(g(x,\xi))\le\max\{\alpha(V(x)),\ \chi(\|\xi\|_U)\}.\tag{3.6}$$
--
--   This is the small-gain theorem for impulsive systems: an ISS-Lyapunov function of the whole interconnection is assembled from those of its subsystems, in the max form of Proposition 3.1, so that the dwell-time theorems of the paper can then be applied to the interconnection.
--
--   **Formalization Note** The conclusion is the form of Proposition 3.1, as Remark 8 states the theorem is formulated, and not Definition 4: the gain $\chi$ of (4.11) is in $\mathcal K$ but need not be in $\mathcal K_\infty$, which Proposition 3.1 requires. The flow bound (3.5) is asserted for $x\ne0$: the printed statement fails at $x=0$ when some $\sigma_i^{-1}$ is not Lipschitz at $0$ (with $n=1$, $\dot x=-x+u$, $V_1=|x|$, $\sigma_1(r)=r^2$, $\xi=0$, $u(t)=\min(t,1)$, one gets $\dot V_u(0)=1/\sqrt2>0$). The page's $\varphi$ (4.12) involves $(\sigma_i^{-1})'$, which exists only almost everywhere, so $\varphi$ and $\alpha$ are existential. Hypothesis (4.5) is taken along the components of the interconnection's own flow, which is what the proof uses. The small-gain condition is kept as a hypothesis as on the page, although the proof uses only the $\Omega$-path (whose existence under (4.9) is quoted from [8]). The system is modelled by the pair $(\phi_c,g)$, the initial time is $0$, and $X$ is the Pi type over `Fin n`, whose own (sup) norm is never used.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 19, Theorem 8, (4.10), (4.11); proof pp. 19–20; Remark 8, p. 20; Proposition 3.1, p. 5

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.SmallGain

/-- Theorem 8 (arXiv:1212.5481v1, p. 19), in the form of Proposition 3.1 (Remark 8, p. 20), with
the flow estimate (3.5) at nonzero states only (the printed statement fails at `x = 0` when some
`σᵢ⁻¹` is not Lipschitz at `0`). Let the subsystems of the interconnection `S` have ISS-Lyapunov
functions `Vᵢ` with gains `χᵢⱼ`, `χᵢ` (items 1–3, p. 18), let `Γ` (4.7) satisfy the small-gain
condition (4.9) and let `σ` be an Ω-path for `Γ` with `τᵢ = σᵢ⁻¹`. Then
`V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))` (4.10) is continuous, satisfies (3.1) for the sum norm on `X`, satisfies
(3.5) with the gain `χ(r) = maxᵢ σᵢ⁻¹(χᵢ(r))` (4.11) and some `φ ∈ 𝒫` at every `x ≠ 0`, and
satisfies (3.6) with the gain `χ` and some `α ∈ 𝒫`. -/
theorem theorem_8 {n : ℕ} {Xi : Fin n → Type*} [∀ i, NormedAddCommGroup (Xi i)]
    [∀ i, NormedSpace ℝ (Xi i)] [∀ i, CompleteSpace (Xi i)]
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveSystem ((i : Fin n) → Xi i) U) (hS : IsImpulsiveSystem S)
    (V : (i : Fin n) → Xi i → ℝ≥0) (ψ₁ ψ₂ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0) (φ α : Fin n → ℝ≥0 → ℝ≥0)
    (hV : IsSubsystemISSLyapunov S V ψ₁ ψ₂ χ χu φ α)
    (hSGC : SmallGainCondition (gainOp χ))
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (gainOp χ) σ τ) :
    Continuous (smallGainV τ V) ∧
    (∃ ψ₁' ψ₂' : ℝ≥0 → ℝ≥0, IsKInf ψ₁' ∧ IsKInf ψ₂' ∧
      ∀ x, ψ₁' (sumNorm x) ≤ smallGainV τ V x ∧ smallGainV τ V x ≤ ψ₂' (sumNorm x)) ∧
    (∃ φ' : ℝ≥0 → ℝ≥0, IsPosDef φ' ∧
      ∀ (x : (i : Fin n) → Xi i) (ξ : U) (u : ℝ → U), x ≠ 0 → IsPCInput u → u 0 = ξ →
        smallGainChi τ χu ‖ξ‖₊ ≤ smallGainV τ V x →
        lieDeriv S (smallGainV τ V) x u ≤ ((-(φ' (smallGainV τ V x)) : ℝ) : EReal)) ∧
    (∃ α' : ℝ≥0 → ℝ≥0, IsPosDef α' ∧
      ∀ (x : (i : Fin n) → Xi i) (ξ : U),
        smallGainV τ V (S.jump x ξ) ≤ max (α' (smallGainV τ V x)) (smallGainChi τ χu ‖ξ‖₊)) := by sorry

end ImpulsiveISS.SmallGain
