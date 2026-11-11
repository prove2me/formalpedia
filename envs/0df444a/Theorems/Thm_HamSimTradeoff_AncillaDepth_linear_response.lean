-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_linear_response
-- name    : HamSimTradeoff.AncillaDepth.linear_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:46.782031+00:00
-- url     : https://prove2.me/theorems/ece0a66d-3b96-4701-a641-15e1640329aa
-- title:
--   §3.1 p.16 — controller moments and full linear-response formula
-- statement:
--   Fix any architecture and any source hard family with $L\ge2$ and admissible weights. Write $\eta$ for the ideal controller amplitude, $\omega_{\ell r}$ for its prefix-suffix weights, $M_n=s^{-1}\sum_{\ell,r}\omega_{\ell r}m_{\ell r}^{-2n}$, and $g$ for the explicit response function. For every round, $\sum_r\omega_{\ell r}=\eta$. For every real $t$,
--   $$\partial_\delta C(t,0)=-\frac{it}{s}\left(\sum_{\ell,r}\omega_{\ell r}\rho_k(t/(sm_{\ell r}))\right)X=\left(-\frac{i\eta t}{2}+g(t)\right)X,$$
--   $$g(t)=-it\sum_{n=k}^{\infty}c_{k,n}(t/s)^{2n}M_n.$$
--   Both displayed matrix derivatives exist and the series converges. For every integer $n\ge k$,
--   $$g^{(2n+1)}(0)=-i(2n+1)!c_{k,n}s^{-2n}M_n.$$
--   This is the link between the actual simulator, its scalar response, and the controller moment sequence. No approximation hypothesis is required for these identities.
--
--   Differences from the source:
--   - encoding: indices 1,…,L, rounds 1,…,s and branches 1,…,R → zero-based Fin indices, with ancilla |0^a⟩ represented by index zero; reason: a bijective relabeling preserves every matrix product and sum
--   - encoding: infinite series beginning at n=k → HasSum of the sequence indexed by n=j+k for j≥0; reason: HasSum records convergence as well as the value and avoids default values for divergent sums
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.16, §3.1, unnumbered linear-response displays and derivative identity; Eq. (3.2), p.15

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- The unnumbered p.16 linear response, including its series and derivative formula. -/
theorem linear_response {L : ℕ} (B : Architecture) (w : HardWeights L) (t : ℝ) :
    (∀ ell : Fin B.s, ∑ r, omega B ell r = eta B) ∧
    HasDerivAt (hardCompression B w t)
      ((-Complex.I * (t : ℂ) / (B.s : ℂ) *
        (∑ ell, ∑ r, omega B ell r *
          (rho B.k (t / ((B.s : ℝ) * B.m ell r)) : ℂ))) • pauliX) 0 ∧
    HasDerivAt (hardCompression B w t)
      ((-Complex.I * eta B * (t : ℂ) / 2 + response B t) • pauliX) 0 ∧
    HasSum (fun j : ℕ => -Complex.I * (t : ℂ) * (coefficient B.k (j + B.k) : ℂ) *
      ((t : ℂ) / (B.s : ℂ)) ^ (2 * (j + B.k)) * moment B (j + B.k)) (response B t) ∧
    (∀ n : ℕ, B.k ≤ n → iteratedDeriv (2 * n + 1) (response B) 0 =
      -Complex.I * (Nat.factorial (2 * n + 1) : ℂ) * (coefficient B.k n : ℂ) *
        ((B.s : ℂ) ^ (2 * n))⁻¹ * moment B n) := by sorry

end HamSimTradeoff.AncillaDepth
