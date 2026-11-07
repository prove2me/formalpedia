-- Prove2me | Theorems.Thm_FreeSpencer_lemma_5_2
-- name    : FreeSpencer.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:48.617208+00:00
-- url     : https://prove2.me/theorems/98eee8ce-da8b-458b-a55c-28fe8128d013
-- title:
--   Lemma 5.2, pp.31–32 — linearized KKT system and exact response
-- statement:
--   At a positive definite density $S$ with $M=\eta_C(S)\succ0$, let $Z\succ0$ solve $ZMZ=S$. The negative Hessian of $S\mapsto2F(S,\eta_C(S))$ is $H_f^{\mathrm{original}}=L^*K^{-1}L$, and the inverse negative Hessian of $2\theta\mathrm{Tr}\sqrt S$ is $B\mapsto\frac1\theta(SB\sqrt S+\sqrt SBS)$. If $S$ also maximizes the square potential at $(H,C)$, then along $H(t)=H+tB$ the optimizers are differentiable and
--   $$K(\dot Z(0))=L(\dot S(0)),\qquad H_\theta^{\mathrm{original}}(\dot S(0))+L^*(\dot Z(0))+\dot\lambda(0)I=B,\qquad\mathrm{Tr}\,\dot S(0)=0;$$
--   with $H^{\mathrm{original}}=H_f^{\mathrm{original}}+H_\theta^{\mathrm{original}}$,
--   $$\frac12D_H^2E(H,C)[B,B]=\frac12\langle B,(H^{\mathrm{original}})^{-1}B\rangle-\frac12\frac{\langle I,(H^{\mathrm{original}})^{-1}B\rangle^2}{\langle I,(H^{\mathrm{original}})^{-1}I\rangle},$$
--   which is at most the unconstrained form $\frac12\langle B,(H^{\mathrm{original}})^{-1}B\rangle$; and the covariance derivative is $\Gamma(u,w)=\mathrm{Tr}(S\hat A(u)Z\hat A(w))$.
--
--   **Formalization Note** $(H^{\mathrm{original}})^{-1}$ on the symmetric matrices is written through symmetric solutions $Y_B$ of $H^{\mathrm{original}}Y_B=B$, which are asserted to exist uniquely.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - encoding: (H^original)⁻¹ on S^D, and L∗ → symmetric solutions Y with opH Y = B, shown to exist uniquely; L∗ is opL; reason: the same inverse on the symmetric subspace; L is self-adjoint for the trace pairing
--   - reading: the optimizing triple (S, Z, λ) along the path (5.2) → S(t) = optDensity, Z(t) = transport S(t) (η_C S(t)), λ(t) = Tr(H(t) + Z⁻¹ + η_C(Z) + θ S^{-1/2})/D; reason: these are the solutions of (5.2): the page gives the formula for Z, and λ I has trace Dλ
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, pp.31–32

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_transport
import Definitions.Def_FreeSpencer_KrausFacts
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 5.2** (Linearized KKT system and exact response), all clauses (5.4)–(5.8).
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 5.2, pp.31–32.

**Formalization Note** Inverses on `S^D` are written through solutions: `Y_B` symmetric with
`H^original(Y_B) = B`, and the second clause group asserts one exists, uniquely. `L∗` is `opL`, since
`L` is self-adjoint. The optimizing path is `S(t) = S(H + tB, C)`, `Z(t)` the transport of `S(t)`
and `η_C(S(t))`, and `λ(t)` the multiplier of (5.2), read off as `Tr(H(t) + Z⁻¹ + η_C(Z) + θ S^{-1/2})/D`.
(5.5), (5.6) use only `S ≻ 0`, `M ≻ 0` and `Z`, as the page's last sentence says. -/
theorem lemma_5_2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (θ : ℝ)
    (hθ : 0 < θ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : C.PosSemidef) :
    (∀ S Z : Matrix ι ι ℝ, S.PosDef → (covMap Ah C S).PosDef → Z.PosDef →
      Z * covMap Ah C S * Z = S →
      IsUnit (opK Z (covMap Ah C S)) ∧
      (∀ X : Matrix ι ι ℝ, X.IsSymm →
        -(deriv (deriv fun t : ℝ => 2 * fidelity (S + t • X) (covMap Ah C (S + t • X))) 0) =
          Matrix.trace (X * opHf Ah C Z (covMap Ah C S) X)) ∧
      (∀ X : Matrix ι ι ℝ, X.IsSymm →
        -(deriv (deriv fun t : ℝ => 2 * θ * Matrix.trace (MatrixLewis.mpow (1 / 2) (S + t • X))) 0) =
          Matrix.trace (X * opHtheta θ S X)) ∧
      (∀ B : Matrix ι ι ℝ, B.IsSymm →
        opHtheta θ S (θ⁻¹ • (S * B * MatrixLewis.mpow (1 / 2) S + MatrixLewis.mpow (1 / 2) S * B * S)) = B ∧
        θ⁻¹ • (S * opHtheta θ S B * MatrixLewis.mpow (1 / 2) S + MatrixLewis.mpow (1 / 2) S * opHtheta θ S B * S) = B)) ∧
    (∀ H S Z : Matrix ι ι ℝ, H.IsSymm → IsMaximizer (1 / 2) θ 0 Ah H C S → S.PosDef →
      (covMap Ah C S).PosDef → Z.PosDef → Z * covMap Ah C S * Z = S →
      let M := covMap Ah C S
      (∀ B : Matrix ι ι ℝ, B.IsSymm →
        let Sp : ℝ → Matrix ι ι ℝ := fun t => optDensity (1 / 2) θ 0 Ah (H + t • B) C
        let Zp : ℝ → Matrix ι ι ℝ := fun t => transport (Sp t) (covMap Ah C (Sp t))
        let lam : ℝ → ℝ := fun t => (Fintype.card ι : ℝ)⁻¹ * Matrix.trace
          (H + t • B + (Zp t)⁻¹ + covMap Ah C (Zp t) + θ • MatrixLewis.mpow (-(1 / 2)) (Sp t))
        ∃ (Zd Sd : Matrix ι ι ℝ) (ld : ℝ), Zd.IsSymm ∧ Sd.IsSymm ∧ HasDerivAt Zp Zd 0 ∧
          HasDerivAt Sp Sd 0 ∧ HasDerivAt lam ld 0 ∧
          opK Z M Zd = opL Ah C Z Sd ∧
          opHtheta θ S Sd + opL Ah C Z Zd + ld • (1 : Matrix ι ι ℝ) = B ∧
          Matrix.trace Sd = 0) ∧
      (∀ B : Matrix ι ι ℝ, B.IsSymm → ∃! Y : Matrix ι ι ℝ, Y.IsSymm ∧ opH θ Ah C S Z M Y = B) ∧
      (∀ B YB YI : Matrix ι ι ℝ, B.IsSymm → YB.IsSymm → YI.IsSymm → opH θ Ah C S Z M YB = B →
        opH θ Ah C S Z M YI = 1 →
        (1 / 2) * centerHess (1 / 2) θ 0 Ah H C B =
          (1 / 2) * Matrix.trace (B * YB) - (1 / 2) * Matrix.trace YB ^ 2 / Matrix.trace YI ∧
        (1 / 2) * centerHess (1 / 2) θ 0 Ah H C B ≤ (1 / 2) * Matrix.trace (B * YB)) ∧
      (∀ u w : Fin ℓ → ℝ, InRan C u → InRan C w →
        covForm (1 / 2) θ 0 Ah H C u w = gammaAt Ah S Z u w)) := by sorry

end FreeSpencer
