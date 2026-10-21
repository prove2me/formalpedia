-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_eq_25_marginal_storage
-- name    : OffGridStorage.TechChoice.eq_25_marginal_storage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:04.529256+00:00
-- url     : https://prove2.me/theorems/01f43456-a8d4-4d17-b1a1-8540fab7fc5c
-- title:
--   Eq. (25), pp. 38–39 — no-storage optimum Q*_F(K=0) and the marginal value of storage there
-- statement:
--   Under the standing assumptions, let $Q_0=D_H\sqrt{g/(2c_Q)}=\sqrt{(g/c_Q)D_H^2/2}$. Then:
--
--   1. $Q_0$ maximizes the no-storage full-discharge profit: $\Pi_F(Q,0)\le \Pi_F(Q_0,0)$ for every $Q\ge 0$.
--   2. For every $Q>0$ and every $K$, the closed form (20) (times $T$) has partial derivative in $K$
--   $$\frac{\partial}{\partial K}=T\Bigl(\frac{g}{Q}\Bigl[-D_H-\frac{K}{e}\Bigr]+g-\frac{c_K}{e}\Bigr).$$
--   3. At $(Q_0,0)$ this derivative equals
--   $$T\Bigl(-\sqrt{2c_Qg}+g-\frac{c_K}{e}\Bigr).$$
--
--   The sign of the last expression decides whether adding a first unit of storage to the best no-storage plan pays; setting it to zero yields the threshold $g_0$.
--
--   **Formalization Note** The paper's derivatives are per period; here the closed form carries the factor $T$, so each derivative carries it too. The derivative in item 2 is a two-sided derivative of the closed-form expression, which is a polynomial in $K$ for fixed $Q>0$.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), pp. 38–39, Appendix A.4.1, eq. (25)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Eq. (25), pp. 38–39: (i) `Q0 = D_H √(g/(2c_Q))` maximizes the no-storage full-discharge
profit over `Q ≥ 0`; (ii) the partial derivative of the closed form in `K` is
`T((g/Q)(-D_H - K/e) + g - c_K/e)`; (iii) at `(Q0, 0)` it equals `T(-√(2 c_Q g) + g - c_K/e)`. -/
theorem eq_25_marginal_storage (p : Params) (hp : Standing p) :
    (0 ≤ Q0 p ∧ ∀ Q : ℝ, 0 ≤ Q → profitF p Q 0 ≤ profitF p (Q0 p) 0) ∧
    (∀ Q K : ℝ, 0 < Q →
      HasDerivAt (fun K' => closedFormF p Q K')
        ((p.T : ℝ) * (p.g / Q * (-p.DH - K / p.e) + p.g - p.cK / p.e)) K) ∧
    HasDerivAt (fun K' => closedFormF p (Q0 p) K')
      ((p.T : ℝ) * (-Real.sqrt (2 * p.cQ * p.g) + p.g - p.cK / p.e)) 0 := by sorry

end OffGridStorage.TechChoice
