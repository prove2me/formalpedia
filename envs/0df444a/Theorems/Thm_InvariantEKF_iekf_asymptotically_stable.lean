-- Prove2me | Theorems.Thm_InvariantEKF_iekf_asymptotically_stable
-- name    : InvariantEKF.iekf_asymptotically_stable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:19:32.028808+00:00
-- url     : https://prove2.me/theorems/34d09717-b888-43e8-bacc-23e204bcd1f2
-- title:
--   Theorem 4 (as proved): the invariant EKF is an asymptotically stable observer about any trajectory
-- statement:
--   Let $G$ be a matrix Lie group with Lie algebra coordinates $\mathcal L_{\mathfrak g}$. Let $\frac{d}{dt}\chi_t=f_{u_t}(\chi_t)$ be group affine, locally Lipschitz in the state uniformly on compact time windows, and forward complete on $G$. It is observed at $t_n=n\,\Delta t$ through left-invariant outputs $Y^i=\chi_{t_n}d^i$ (resp. right-invariant outputs $Y^i=\chi_{t_n}^{-1}d^i$), $i=1,\dots,k$. Let $A_{u_t}$ be defined by $g_{u_t}(\exp\xi)=\mathcal L_{\mathfrak g}(A_{u_t}\xi)+O(\|\xi\|^2)$ for $g=g^L$ (resp. $g^R$), and let $H$ be the observation matrix of the filter. The design matrices $\hat Q_t(\cdot)$ and $\hat N_n(\cdot)$ are positive semidefinite functions of the estimate.
--
--   Fix a true trajectory $\chi_t$, $t\ge0$. Suppose the Deyst-Price conditions (i)-(v) of Theorem 3 hold for $(A_{u_t},H,\hat Q_t(\chi_t),\hat N_n(\chi_{t_n}))$, i.e. for the system linearized about the **true** trajectory, with positive constants. Suppose also that the transition matrix of $A_{u_t}$ is bounded on each sampling interval, and that $\hat Q,\hat N$ evaluated at nearby estimates are comparable with their values on $\chi_t$ (for every $\kappa>1$ there is $\varepsilon>0$ such that an invariant error $\exp\xi$ with $\|\xi\|<\varepsilon$ gives $\kappa^{-1}\hat Q_t(\chi_t)\preceq\hat Q_t(\hat\chi_t)\preceq\kappa\hat Q_t(\chi_t)$, and likewise for $\hat N_n$). Fix $P_0\succ0$.
--
--   Then the Left (resp. Right) Invariant EKF (36)-(37) is an asymptotically stable observer of $\chi_t$, with a radius independent of the initialization time. There is $\varepsilon>0$ such that, for every $t_0\ge0$ and every initial estimate $\hat\chi_{t_0}\in G$ with $P_{t_0}=P_0$,
--
--   $$\|\chi_{t_0}^{-1}\hat\chi_{t_0}-I\|_F<\varepsilon\ \Longrightarrow\ \|\chi_t^{-1}\hat\chi_t-I\|_F\to0\quad(t\to\infty)$$
--
--   (resp. with $\hat\chi\chi^{-1}$ in place of $\chi^{-1}\hat\chi$).
--
--   **Formalization Note** This is Theorem 4 as the proof in Appendix C establishes it. (a) $H$ has the sign of the paper's worked examples. With the sign printed in Section 3.3 the filter diverges, even for $G=\mathbb R_{>0}$. (b) Condition (v) of Theorem 3 is in the form of Deyst and Price. (c) The bounded-transition condition supplies the bounds $\gamma_{\min}I\preceq P_t\preceq\gamma_{\max}I$ for all $t$ that Lemmas 5-7 use. (d) The comparability of $\hat Q,\hat N$ is the inequality the proof of Lemma 4 asserts. It fails for the paper's general form $Q_1+Ad_{\hat\chi^{-1}}Q_2Ad^T_{\hat\chi^{-1}}$ when $Q_2$ is singular. (e) The distance of Definition 2 is measured through the invariant error. (f) The same $P_0$ is used at every initialization time.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Section 3.4, Theorem 4, p. 13, with the filter of eqs. (36)-(37), p. 12, Definition 2, p. 13; proof in Appendix C, pp. 27-31

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem iekf_asymptotically_stable {N d K : ℕ} {U : Type*} (left : Bool)
    (G : Set (Matrix (Fin N) (Fin N) ℝ)) (hG : IsMatrixLieGroup G)
    (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ) (hL : IsLieAlgebraCoords G L)
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : IsGroupAffine G f)
    (u : ℝ → U) (hreg : IsLocLipschitzField (fun t => f (u t)))
    (hcomplete : ∀ a ∈ G, ∃ χ, IsTrajectory G f u (Set.Ici 0) χ ∧ χ 0 = a)
    (A : U → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ t, 0 ≤ t → IsLinearization L (errField left f (u t)) (A (u t)))
    (dvec : Fin K → Fin N → ℝ) (dt : ℝ) (hdt : 0 < dt)
    (Qhat : ℝ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Nhat : ℕ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin K × Fin N) (Fin K × Fin N) ℝ)
    (hQ : ∀ t X, (Qhat t X).PosSemidef) (hN : ∀ n X, (Nhat n X).PosSemidef)
    (χ : ℝ → Matrix (Fin N) (Fin N) ℝ) (hχ : IsTrajectory G f u (Set.Ici 0) χ)
    (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) (hPhi : IsTransitionMatrix (fun t => A (u t)) Phi)
    (α₁ α₂ β₁ β₂ δ₁ δ₂ δ₃ c : ℝ) (M : ℕ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hM : 1 ≤ M)
    (hDP : DeystPriceConditions dt Phi (fun s => Qhat s (χ s)) (obsH left L dvec)
      (fun n => Nhat n (χ ((n : ℝ) * dt))) α₁ α₂ β₁ β₂ δ₁ δ₂ δ₃ M)
    (hbdd : BoundedTransition dt Phi c)
    (hcomp : TuningComparable left L χ dt Qhat Nhat)
    (P0 : Matrix (Fin d) (Fin d) ℝ) (hP0 : P0.PosDef) :
    ∃ ε > 0, ∀ t0 : ℝ, 0 ≤ t0 → ∀ χhat0 ∈ G,
      ∀ (xs : ℕ → ℝ → Matrix (Fin N) (Fin N) ℝ) (Ps : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ),
        IsIEKFRun left L f u A dvec dt Qhat Nhat χ t0 χhat0 P0 xs Ps →
        invErrDist left (χ t0) χhat0 < ε →
        Tendsto (fun t => invErrDist left (χ t) (piecewiseRun xs dt t)) atTop (𝓝 0) := by sorry

end InvariantEKF
