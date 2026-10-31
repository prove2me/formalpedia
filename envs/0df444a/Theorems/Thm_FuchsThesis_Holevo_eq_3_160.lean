-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_160
-- name    : FuchsThesis.Holevo.eq_3_160
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:06.015411+00:00
-- url     : https://prove2.me/theorems/f3adb6f6-4686-41fe-8336-3d0067731bbc
-- title:
--   Eq. (3.160) with (3.162)–(3.163): $S''(t)=-\sum_{\lambda_j+\lambda_k\ne0}\Phi(\lambda_j,\lambda_k)|\Delta_{jk}|^2$
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional space and $0<t<1$. Let $\lambda_j$ be the eigenvalues of $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$ with orthonormal eigenvectors $|j\rangle$, and $\Delta_{jk}=\langle j|\hat\Delta|k\rangle$ with $\hat\Delta=\hat\rho_1-\hat\rho_0$. Then the Holevo quantity $S(t)$ of (3.149) is twice differentiable at $t$ and
--
--   $$
--   S''(t) = -\sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \Phi(\lambda_j,\lambda_k)\,|\Delta_{jk}|^2 ,
--   $$
--
--   where $\Phi(x,y)=(\ln x-\ln y)/(x-y)$ for $x\ne y$ and $\Phi(x,x)=1/x$.
--
--   It shows that $S$ is concave and is half of the curvature comparison $S''\le L''$.
--
--   **Formalization Note** For a pair with $\lambda_j=0<\lambda_k$ the true $\Phi$ is $+\infty$ while Lean's closed form (with $\ln0=0$) is finite; for $0<t<1$ such pairs have $\Delta_{jk}=0$, so the term is $0$ either way.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - reading: S″(t) at the channel parameter t → t ∈ (0, 1); reason: the functions are defined on [0, 1] only, so a second derivative is two-sided only inside; at t ∈ {0, 1} the value can be infinite (ρ0 = |0⟩⟨0|, ρ1 = 1/2 on a qubit: an eigenvalue of ρ is t/2 with Δ-component 1/2, so the term is 1/(2t) → ∞), and the source's derivation of (3.179)–(3.183) assumes 0 < t < 1
--   - encoding: S″(t) → S differentiable at t and HasDerivAt (deriv S) (value) t; reason: the same assertion
--   - encoding: Φ defined by the contour integral (3.161) and evaluated in (3.162)–(3.163) → Φ defined directly by the closed form (3.162)–(3.163); reason: the source's own evaluation; the same function on positive arguments
--   - encoding: an eigenbasis |j⟩ of ρ̂ → the columns of Mathlib's eigenvectorUnitary of ρ̂; reason: the sum is independent of the choice of eigenbasis
--   - encoding: Φ(λ_j, λ_k) = +∞ for a pair with λ_j = 0 < λ_k → Lean's phi is finite there (Real.log 0 = 0); reason: for 0 < t < 1 every such pair has Δ_jk = 0 (3.179), so its term is 0 either way and no instance changes
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.160) with (3.162)–(3.163), p.67 (PDF p.76)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_eigval
import Definitions.Def_FuchsThesis_Holevo_eigCoord
import Definitions.Def_FuchsThesis_Holevo_holevoS
import Definitions.Def_FuchsThesis_Holevo_phi

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.160) with (3.162)–(3.163), p.67 (PDF p.76): for
density operators `ρ̂0, ρ̂1` and `t ∈ (0, 1)`, the Holevo quantity `S(t)` (3.149) is twice
differentiable at `t` and
`S″(t) = −∑_{j,k | λ_j + λ_k ≠ 0} Φ(λ_j, λ_k) |Δ_jk|²`,
where `λ_j` are the eigenvalues of `ρ̂ = (1 − t)ρ̂0 + tρ̂1`, `|j⟩` an orthonormal eigenbasis,
`Δ_jk = ⟨j|Δ̂|k⟩`, `Δ̂ = ρ̂1 − ρ̂0`, and `Φ` is given by (3.162)–(3.163).

**Formalization Note.** Stated as: `S` is differentiable at `t`, and `deriv S` has derivative
equal to the right side at `t`. `Φ` is the closed form `phi` (the source's contour integral (3.161)
evaluated). For a pair with `λ_j = 0 < λ_k` the true `Φ` is `+∞` while Lean's `phi` (with
`Real.log 0 = 0`) is finite; for `0 < t < 1` such pairs have `Δ_jk = 0` (3.179), so the term is `0`
either way. -/
theorem eq_3_160 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun s => holevoS ρ0 ρ1 s) t ∧
      HasDerivAt (deriv (fun s => holevoS ρ0 ρ1 s))
        (-∑ j, ∑ k,
          if eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k ≠ 0 then
            phi (eigval (mixState ρ0 ρ1 t) j) (eigval (mixState ρ0 ρ1 t) k) *
              ‖eigCoord (mixState ρ0 ρ1 t) (ρ1 - ρ0) j k‖ ^ 2
          else 0)
        t := by sorry

end FuchsThesis.Holevo
