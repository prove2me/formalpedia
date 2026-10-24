-- Prove2me | Theorems.Thm_HILL_PRG_inverter_check_advantage_bound
-- name    : HILL.PRG.inverter_check_advantage_bound
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-24T04:53:45.510977+00:00
-- url     : https://prove2.me/theorems/d66b4b27-5dad-48de-a67b-03146876a627
-- title:
--   Inversion checking gives at least half the inverter success as distinguishing advantage
-- statement:
--   Let $G_n$ map $t(n)$-bit seeds to $\ell(n)$-bit outputs, with $t(n)<\ell(n)$. Let $A$ be an inverter and $B$ a checker using the same independent random coins. On input an image $y$, the checker accepts exactly when $A$ returns a seed of the required length whose image under $G_n$ is $y$. Then
--
--   $$
--   \Pr[A\text{ inverts }G_n(U_{t(n)})]\leq
--   2\left|\Pr[B(G_n(U_{t(n)}))=1]-\Pr[B(U_{\ell(n)})=1]\right|.
--   $$
--
--   This is the finite probability bound underlying the reverse implication of the HILL equivalence. It requires exact output lengths and the stated checker behavior; polynomial-time construction of the checker is a separate computational obligation.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Håstad, Impagliazzo, Levin, Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, p. 1387, Theorem 6.3, reverse implication attributed to Levin (1987); https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf. The checking algorithm and quantitative counting bound are an explicit formalization of the standard inverter-to-distinguisher reduction.

import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

theorem inverter_check_advantage_bound (G : FunEns) (A B : Adv)
    (hlen : ∀ n x, x ∈ cube (G.t n) → (G.f 0 n x).length = G.ℓ n)
    (hcoins : B.coins = A.coins)
    (hcheck : ∀ n y r, y ∈ cube (G.ℓ n) → r ∈ cube (A.coins n) →
      (B.run (encAdvice n 0 (y ++ r)) = [true] ↔
        let out := A.run (enc n (y ++ r));
        out ∈ cube (G.t n) ∧ G.f 0 n out = y))
    (n : ℕ) (hstr : G.t n < G.ℓ n) :
    invSucc G A n ≤ 2 * advantage B n (fun _ => 0) (G.ℓ n)
      (G.law (fun _ => 0) n) (uniformBits (G.ℓ n)) := by sorry

end HILL.PRG
