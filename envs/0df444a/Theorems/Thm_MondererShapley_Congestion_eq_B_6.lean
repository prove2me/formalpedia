-- Prove2me | Theorems.Thm_MondererShapley_Congestion_eq_B_6
-- name    : MondererShapley.Congestion.eq_B_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:50.710108+00:00
-- url     : https://prove2.me/theorems/3f9564d0-08ff-48c5-96b6-bc6f98fb77b1
-- title:
--   (B.6) — $x^1(A^i_{m_i}\cap A(-i)^c) = x^1(\varepsilon(m^i)) = u^i(a) - P(a)$
-- statement:
--   Let $\Gamma$ be a finite game with players $N = \{1,\dots,n\}$, finite strategy sets $Y^i$, payoffs $u^i$, and let $P$ be a potential for $\Gamma$. On the facility set $M$ of the proof of Theorem 3.2, let $A^i_l$, $\varepsilon(m^i)$, $M_2$ (B.5) and the vector $x^1$ be as defined on pp. 140–141, with $Q^i$ of (B.4). Then for every $m = (m_1, \dots, m_n) \in K$, with $A = (A^1_{m_1}, \dots, A^n_{m_n}) \in \Sigma$, $a = (a^1_{m_1}, \dots, a^n_{m_n})$ and $m^i = (m_k)_{k\neq i}$,
--
--   $$x^1\big(A^i_{m_i}\cap A(-i)^c\big) = x^1\big(\varepsilon(m^i)\big) = u^i(a) - P(a) \qquad \text{for every } i \in N, \tag{B.6}$$
--
--   where $A(-i) = \bigcup_{k\neq i} A^k_{m_k}$ and $x(B) = \sum_{j\in B} x(j)$.
--
--   Together with (B.2) and Lemma B.1, (B.6) shows that the congestion game built in the proof reproduces the payoffs of $\Gamma$.
--
--   **Formalization Note.** Two misprints of the page are corrected: the printed $x^1(A^i_{m_i}\cap A(-i))$ is $x^1(A^i_{m_i}\cap A(-i)^c)$, the set of the $x^1$ term of Lemma B.1 (the facility $\varepsilon(m^i)$ lies in $A^i_{m_i}$ and in no $A^k_{m_k}$, $k\neq i$), and the printed $P^i(a)$ is $P(a)$. $K(i)$ is identified with $Y^i$.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 141 (PDF p. 18), (B.6)

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
import Definitions.Def_MondererShapley_Congestion_FacilityConstruction

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 141, (B.6): let `P` be a potential for the finite game `Γ`. For every
`m = (m₁, …, mₙ) ∈ K`, with `A = (A¹_{m₁}, …, Aⁿ_{mₙ})` and `a = (a¹_{m₁}, …, aⁿ_{mₙ})`,
`x¹(Aⁱ_{m_i} ∩ A(−i)^c) = x¹(ε(mⁱ)) = uⁱ(a) − P(a)` for every player `i`, where `mⁱ = (m_k)_{k≠i}` and
`A(−i) = ∪_{k≠i} Aᵏ_{m_k}`.

**Formalization Note.** Two misprints are corrected: the printed `A(−i)` is `A(−i)^c` (the set of
Lemma B.1's `x¹` term; `ε(mⁱ)` lies in `Aⁱ_{m_i}` and in no `Aᵏ_{m_k}`, `k ≠ i`), and the printed
`Pⁱ(a)` is `P(a)`. `K(i)` is identified with `Yⁱ`. -/
theorem eq_B_6 {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ)
    (hP : MondererShapley.ClosedPath.IsPotential u P) (m : ∀ i, Y i) (i : ι) :
    vecSum (x1 u P) (stratFac i (m i) ∩ (⋃ k ∈ {k | k ≠ i}, stratFac k (m k))ᶜ) =
        x1 u P (epsMinus i m) ∧
      x1 u P (epsMinus i m) = u i m - P m := by sorry

end MondererShapley.Congestion
