-- Prove2me | Theorems.Thm_OpenPitMIP_Vrhs_theorem_7
-- name    : OpenPitMIP.Vrhs.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:18.043975+00:00
-- url     : https://prove2.me/theorems/2ed1fb5e-3c13-4e63-a256-3ef252768594
-- title:
--   Theorem 7, p. 1434 — the VRHS production cut (32) along a chain c₁ ≺ ⋯ ≺ c_n is valid for PCPSP-F, and for PCPSP-P under (33)
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions. Fix a destination $d\in\mathcal D$, a period $t\in\mathcal T$ and clusters $c_1,\dots,c_n\in\mathcal C$ ($n\ge 1$) such that
--
--   1. $c_1\prec c_2\prec\dots\prec c_n$,
--   2. $q(rcl(c_1)\setminus rcl(c_n))<U^d_t$,
--   3. $q(rcl(c_1))>U^d_t$.
--
--   Let $\Delta_k=rcl(c_k)\setminus rcl(c_{k+1})$ and $\delta_k=q(\Delta_k)$ for $k=1,\dots,n-1$, and $\Delta_n=rcl(c_n)$, $\delta_n=U^d_t-q(rcl(c_1)\setminus rcl(c_n))$. Let $0\le\alpha_b\le 1$ for $b\in c_n$, and consider, with $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$, the inequality
--   $$\sum_{k=1}^{n-1}\Big(\sum_{c\in\Delta_k}\sum_{b\in c}q_b y_{b,d,t}\Big)+\sum_{b\in c_n}\alpha_b q_b y_{b,d,t}+\sum_{c\in rcl(c_n)\setminus\{c_n\}}\sum_{b\in c}q_b y_{b,d,t}\ \le\ \sum_{k=1}^{n}\delta_k w_{c_k,t}.\tag{32}$$
--   Then (32) holds at every $(x,y)$ feasible for the PCPSP-F that satisfies the destination capacity rows (9). If moreover
--   $$\sum_{b\in c_n}\alpha_b q_b\ \le\ U^d_t-q(rcl(c_1)\setminus rcl(c_n)),\tag{33}$$
--   then (32) holds at every $(x,y)$ feasible for the PCPSP-P that satisfies (9).
--
--   The VRHS cuts couple the precedence structure along a chain with the capacity of one destination: they tighten the linear relaxation of the PCPSP-C at points that send heavy successors of a partially extracted cluster to a capacitated destination.
--
--   **Formalization Note** "Valid for PCPSP-F (PCPSP-P)" is read as: valid at every point feasible for (1)–(7) with integrality (10) (resp. (11)) whose side constraints $Gy\le g$ include the destination capacity rows (9) (p. 1427: "constraints (5) typically include conditions of the form (8), (9)"); (9) is an explicit hypothesis. Condition 1 is stated for consecutive pairs; the chain is `c : ℕ → C` read at $1,\dots,n$. Periods are `Fin T` (index $t$ is period $t+1$); $y$ is taken at the single period $t$ and $w$ is cumulative.
-- source:
--   Oper. Res. 68(5), §5.2.2, Theorem 7, (32)–(33), p. 1434

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace OpenPitMIP.Vrhs

open PCPSPC

/-- Theorem 7, Oper. Res. 68(5), p. 1434: for a destination `d`, a period `t` and a chain of
clusters `c₁ ≺ c₂ ≺ ⋯ ≺ c_n` with `q(rcl(c₁) \ rcl(c_n)) < U_t^d < q(rcl(c₁))`, and constants
`0 ≤ α_b ≤ 1` (`b ∈ c_n`), the VRHS inequality (32) is valid for the PCPSP-F; if moreover (33)
`∑_{b ∈ c_n} α_b q_b ≤ U_t^d − q(rcl(c₁) \ rcl(c_n))` holds, (32) is valid for the PCPSP-P.
Validity is over feasible points that also satisfy the destination capacity rows (9). -/
theorem theorem_7 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t : Fin T) (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → C)
    (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1)))
    (h2 : I.qSet (I.rcl (c 1) \ I.rcl (c n)) < I.Ud d t)
    (h3 : I.Ud d t < I.qSet (I.rcl (c 1)))
    (α : B → ℝ) (hα : ∀ b ∈ I.blocksOf {c n}, 0 ≤ α b ∧ α b ≤ 1) :
    (∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ), I.Feasible .F x y → I.DestCap y →
      I.vrhsLHS d t c n α y ≤ I.vrhsRHS d t c n x) ∧
    (∑ b ∈ I.blocksOf {c n}, α b * I.q b ≤ I.Ud d t - I.qSet (I.rcl (c 1) \ I.rcl (c n)) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ), I.Feasible .P x y → I.DestCap y →
        I.vrhsLHS d t c n α y ≤ I.vrhsRHS d t c n x) := by sorry

end OpenPitMIP.Vrhs
