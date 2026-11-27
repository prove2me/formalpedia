-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_7
-- name    : IncentiveFinNet.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:34:41.067016+00:00
-- url     : https://prove2.me/theorems/7f912095-39f9-49c5-a410-79ebfafcaa2c
-- title:
--   Theorem 7 — comparative statics of the stable network in $M$, $c\Sigma$ and $\Sigma'\succ\Sigma$ (corrected: eigenpairs of $\Gamma^{-1/2}\Sigma\Gamma^{-1/2}$; $M+M^{\top}\neq0$ in part 3)
-- statement:
--   Consider network settings in which all agents share the covariance $\Sigma_i=\Sigma\succ0$ and all edges are allowed, with risk aversions $\gamma_i>0$ and $\Gamma = \mathrm{diag}(\gamma_i)$. Write $W = W(M)$ for the stable network of the setting with expected returns $M$ (it exists and is unique by Corollary 2 and Theorem 1).
--
--   1. **Change in beliefs about expected returns.** Let $\Gamma^{-1/2}\Sigma\Gamma^{-1/2} = V\Lambda V^{\top}$ with $V$ orthogonal and $\Lambda = \mathrm{diag}(\lambda_1,\dots,\lambda_n)$. Then for all $i,j,k,\ell\in[n]$,
--   $$
--   \frac{\partial W_{ij}}{\partial M_{k\ell}} = \frac{1}{2\sqrt{\gamma_i\gamma_j\gamma_k\gamma_\ell}}\sum_{s,t\in[n]}\frac{V_{is}V_{ks}V_{jt}V_{\ell t}+V_{is}V_{\ell s}V_{jt}V_{kt}}{\lambda_s+\lambda_t}. \qquad (3)
--   $$
--   In particular, $W_{ij}$ is strictly increasing in $M_{ij}$.
--   2. **Risk scaling.** If the covariance $\Sigma$ changes to $c\Sigma$ with $c>0$, the stable network changes from $W$ to $(1/c)W$.
--   3. **Increase in perceived risk.** Suppose $\gamma_i = \gamma$ for all $i$, the covariance increases to $\Sigma'$ with $\Sigma'-\Sigma\succ0$, and $M+M^{\top}\neq0$. If $W$ and $W'$ are the stable networks under $\Sigma$ and $\Sigma'$, then
--   $$
--   \mathrm{tr}\bigl(M^{\top}(W'-W)\bigr) < 0 .
--   $$
--
--   So an increase in perceived risk lowers the belief-weighted average of contract sizes, although individual contracts may grow.
--
--   Differences from the source:
--
--   - correction: part 1: "Let Σ have the eigendecomposition Σ = VΛVᵀ" → V, Λ from the eigendecomposition Γ^{−1/2}ΣΓ^{−1/2} = VΛVᵀ (V orthogonal); reason: with the printed decomposition (3) is false unless Γ = I: for n = 1, Σ = (1), γ = 2 the stable network is W = M/4, so ∂W/∂M = 1/4, while (3) with V = (1), λ = 1 gives 1/8; the proof (A.13, p.48) uses the eigenpairs of Γ^{−1/2}ΣΓ^{−1/2} with V_ij = e_iᵀv_j, and with them (3) is exact. No case is excluded
--   - correction: part 3 for every M → part 3 under the extra premise M + Mᵀ ≠ 0; reason: if M + Mᵀ = 0 (e.g. M = 0) both stable networks are 0 and tr(Mᵀ(W′ − W)) = 0, not < 0; the proof (p.49) needs vec(M + Mᵀ) ≠ 0 for the strict inequality. Excluded case: M with M + Mᵀ = 0
--   - reading: "Suppose Σ_i = Σ for all firms" → shared Σ and all edges allowed (sharedSetting); reason: the proof invokes Corollary A.4 (= Corollary 2, which assumes Ψ_i = I_n) in every part; with prohibited edges (3) is not the derivative of the stable network
--   - reading: "W_ij is monotonically increasing with respect to M_ij" → StrictMono (h ↦ W(M + h e_ie_jᵀ)_ij) for every M; reason: the proof shows ∂W_ij/∂M_ij > 0 and W is linear in M, so the increase is strict; the strict reading is the stronger one
--   - encoding: W as a function of M; ∂W_ij/∂M_kℓ; "W changes to (1/c)W"; "the stable points under Σ and Σ′" → any choice Wf of a stable network for each M, with HasDerivAt of h ↦ Wf(M + h e_ke_ℓᵀ)_ij at 0 for every M; (1/c)W is a stable network under cΣ and every stable network under cΣ equals (1/c)W; every stable W under Σ and W′ under Σ′; reason: the stable network is unique, so every choice is the paper's W(M); same instances
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 7, p.19; restated and proved in A.13, pp.48–49

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_sharedSetting

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 7**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, §3.2, p.19 (restated and proved
in A.13, pp.48–49): "Suppose `Σ_i = Σ` for all firms, and let `M` be the matrix of expected
returns.
1. Change in beliefs about expected returns: Let `Σ` have the eigendecomposition `Σ = VΛVᵀ`. Then
for `i, j, k, ℓ ∈ [n]`, `∂W_ij/∂M_kℓ = 1/(2√(γ_iγ_jγ_kγ_ℓ)) Σ_{s,t∈[n]}
(V_isV_ksV_jtV_ℓt + V_isV_ℓsV_jtV_kt)/(λ_s + λ_t)` (3). In particular, `W_ij` is monotonically
increasing with respect to `M_ij`.
2. Risk scaling: If the covariance `Σ` changes to `cΣ` (`c > 0`), then `W` changes to `(1/c)W`.
3. Increase in perceived risk: Suppose `γ_i = γ` for all `i`, and the covariance `Σ` increases to
`Σ′ ≻ Σ`. Let `W` and `W′` be the stable points under `Σ` and `Σ′` respectively. Then,
`tr(Mᵀ(W′ − W)) < 0`."

Stated in the setting `sharedSetting M Σ γ` (shared `Σ`, all edges allowed), for every `Σ ≻ 0`
and `γ > 0`:
1. (a) for every orthogonal `V` and real `λ` with `Γ^{−1/2}ΣΓ^{−1/2} V = V diag(λ)` and every
   choice `W(·)` of a stable network for each `M`, the derivative of `h ↦ W(M + h e_k e_ℓᵀ)_ij` at
   `0` is (3); (b) `h ↦ W(M + h e_i e_jᵀ)_ij` is strictly increasing;
2. for every `c > 0` and stable `(W, P)` under `Σ`, `(1/c)W` is a stable network under `cΣ` and
   every stable network under `cΣ` equals `(1/c)W`;
3. if `γ_i = γ` for all `i`, `Σ′ − Σ ≻ 0` and `M + Mᵀ ≠ 0`, then `tr(Mᵀ(W′ − W)) < 0` for all
   stable networks `W` under `Σ` and `W′` under `Σ′`.

**Formalization Note**
* Part 1 uses the eigendecomposition of `Γ^{−1/2}ΣΓ^{−1/2}`, as the proof does (A.13, p.48: "Let
  `(λ_i, v_i)` denote the `i`th eigenvalue and eigenvector of `Γ^{−1/2}ΣΓ^{−1/2}`, and let
  `V_ij = e_iᵀv_j`"), not that of `Σ`. With the printed `Σ = VΛVᵀ`, (3) is false unless `Γ = I`:
  for `n = 1`, `Σ = (1)`, `γ = 2`, the stable network is `W = M/4`, so `∂W/∂M = 1/4`, while (3)
  with `V = (1)`, `λ = 1` gives `1/8`.
* Part 3 adds `M + Mᵀ ≠ 0`: for `M + Mᵀ = 0` both stable networks are `0` and the trace is `0`.
* The theorem is read in Corollary 2's setting (all edges allowed): the proof invokes Corollary A.4
  (= Corollary 2) for every part.
* "Monotonically increasing" is stated as `StrictMono`. `e_k e_ℓᵀ` is
  `vecMulVec (Pi.single k 1) (Pi.single ℓ 1)`; `Σ′ ≻ Σ` is `(Σ′ − Σ).PosDef`. -/
theorem theorem_7 {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i)
    (hSig : Sig.PosDef) :
    (∀ (lam : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℝ),
      Vᵀ * V = 1 → (GamInvSqrt γ * Sig * GamInvSqrt γ) * V = V * Matrix.diagonal lam →
      ∀ Wf : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ,
        (∀ M', ∃ P, Stable (sharedSetting M' Sig γ hγ hSig) (Wf M') P) →
        ∀ (M : Matrix (Fin n) (Fin n) ℝ) (i j k l : Fin n),
          HasDerivAt
            (fun h : ℝ => Wf (M + h • vecMulVec (Pi.single k 1) (Pi.single l 1)) i j)
            (1 / (2 * Real.sqrt (γ i * γ j * γ k * γ l)) *
              ∑ s, ∑ t, (V i s * V k s * V j t * V l t + V i s * V l s * V j t * V k t) /
                (lam s + lam t)) 0) ∧
    (∀ Wf : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ,
      (∀ M', ∃ P, Stable (sharedSetting M' Sig γ hγ hSig) (Wf M') P) →
      ∀ (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n),
        StrictMono (fun h : ℝ => Wf (M + h • vecMulVec (Pi.single i 1) (Pi.single j 1)) i j)) ∧
    (∀ (c : ℝ) (Sig' : Matrix (Fin n) (Fin n) ℝ) (hSig' : Sig'.PosDef), 0 < c → Sig' = c • Sig →
      ∀ M W P : Matrix (Fin n) (Fin n) ℝ, Stable (sharedSetting M Sig γ hγ hSig) W P →
        (∃ P', Stable (sharedSetting M Sig' γ hγ hSig') (c⁻¹ • W) P') ∧
        ∀ W' P' : Matrix (Fin n) (Fin n) ℝ, Stable (sharedSetting M Sig' γ hγ hSig') W' P' →
          W' = c⁻¹ • W) ∧
    (∀ g : ℝ, (∀ i, γ i = g) →
      ∀ (Sig' : Matrix (Fin n) (Fin n) ℝ) (hSig' : Sig'.PosDef), (Sig' - Sig).PosDef →
        ∀ M : Matrix (Fin n) (Fin n) ℝ, M + Mᵀ ≠ 0 →
          ∀ W P W' P' : Matrix (Fin n) (Fin n) ℝ, Stable (sharedSetting M Sig γ hγ hSig) W P →
            Stable (sharedSetting M Sig' γ hγ hSig') W' P' →
            Matrix.trace (Mᵀ * (W' - W)) < 0) := by sorry

end IncentiveFinNet.Supplement
