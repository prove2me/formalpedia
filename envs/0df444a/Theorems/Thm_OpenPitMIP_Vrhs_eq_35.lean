-- Prove2me | Theorems.Thm_OpenPitMIP_Vrhs_eq_35
-- name    : OpenPitMIP.Vrhs.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:34.879003+00:00
-- url     : https://prove2.me/theorems/54516e47-ed12-48c5-bd0a-a7ea63b22967
-- title:
--   (35), proof of Theorem 7, p. 1435 — along a chain c₁ ≺ ⋯ ≺ c_n, ∑_{c∈Δ_k}∑_{b∈c} q_b y_{b,d,t} ≤ δ_k w_{c_k,t} for k < n
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, a destination $d$, a period $t$, and clusters $c_1\prec c_2\prec\dots\prec c_n$ ($n\ge 1$). For $k=1,\dots,n-1$ let $\Delta_k=rcl(c_k)\setminus rcl(c_{k+1})$ and $\delta_k=q(\Delta_k)$. Let $(x,y)$ be feasible for the PCPSP-C under either integrality condition, and $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$. Then
--   $$\sum_{c\in\Delta_k}\sum_{b\in c}q_b\,y_{b,d,t}\ \le\ \delta_k\,w_{c_k,t}\qquad\forall k\in\{1,\dots,n-1\}.\tag{35}$$
--
--   This bounds the production sent to $d$ in period $t$ from the "layer" $\Delta_k$ of the chain by the cumulative extraction of the layer's root $c_k$; it is the per-layer estimate in the proof of Theorem 7.
--
--   **Formalization Note** Conditions 2 and 3 of Theorem 7 and the integrality condition play no role in (35) and are not assumed; the statement holds under both integrality conditions. The chain is `c : ℕ → C` read at $1,\dots,n$, and condition 1 is stated for consecutive pairs ($\prec$ is transitive).
-- source:
--   Oper. Res. 68(5), proof of Theorem 7, (35), p. 1435

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace OpenPitMIP.Vrhs

open PCPSPC

/-- (35), proof of Theorem 7, Oper. Res. 68(5), p. 1435: along a chain `c₁ ≺ ⋯ ≺ c_n`, every
feasible `(x, y)` of the PCPSP-C (either integrality condition) satisfies
`∑_{c ∈ Δ_k} ∑_{b ∈ c} q_b y_{b,d,t} ≤ δ_k w_{c_k,t}` for `k = 1, …, n − 1`. -/
theorem eq_35 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t : Fin T) (n : ℕ) (hn : 1 ≤ n)
    (c : ℕ → C) (h1 : ∀ k ∈ Finset.Ico 1 n, I.cprec (c k) (c (k + 1)))
    (κ : OpenPitMIP.UltPit.Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    ∀ k ∈ Finset.Ico 1 n,
      ∑ b ∈ I.blocksOf (I.Delta c n k), I.q b * y b d t ≤ I.delta d t c n k * cum x (c k) t := by sorry

end OpenPitMIP.Vrhs
