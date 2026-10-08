-- Prove2me | Theorems.Thm_MondererShapley_Congestion_eq_B_2
-- name    : MondererShapley.Congestion.eq_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:05.257445+00:00
-- url     : https://prove2.me/theorems/b17cc122-359f-4d59-abff-61e68cd8a022
-- title:
--   Proof of Theorem 3.2, p. 141 — $A^1_{m_1}\cap\cdots\cap A^n_{m_n}\cap M_1 = \{\varepsilon(m)\}$, so $x^n$ satisfies (B.2)
-- statement:
--   Let $\Gamma$ be a finite game with players $N = \{1,\dots,n\}$, finite strategy sets $Y^i$ and a function $P : Y \to \mathbb{R}$. On the facility set $M = \times_{i} \{0,1\}^{K(i)}$ of the proof of Theorem 3.2, let $A^i_l = \{\varepsilon \in M : \varepsilon^i_l = 1\}$, let $\varepsilon(m)$ and $M_1 = \{\varepsilon(m) : m \in K\}$ be as in (B.3), and let $x^n(\varepsilon) = P(a^1_{m_1}, \dots, a^n_{m_n})$ if $\varepsilon = \varepsilon(m) \in M_1$ and $x^n(\varepsilon) = 0$ otherwise. Then for every $m = (m_1, \dots, m_n) \in K$:
--
--   1. $$A^1_{m_1}\cap A^2_{m_2}\cap\cdots\cap A^n_{m_n}\cap M_1 = \{\varepsilon(m)\};$$
--   2. $x^n$ satisfies (B.2):
--   $$x^n\big(A^1_{m_1}\cap A^2_{m_2}\cap\cdots\cap A^n_{m_n}\big) = P(a^1_{m_1}, a^2_{m_2}, \dots, a^n_{m_n}),$$
--   where $x(B) = \sum_{j \in B} x(j)$.
--
--   In the congestion game built in the proof, (B.2) makes the facilities used by all $n$ players carry exactly the potential.
--
--   **Formalization Note.** $K(i)$ is identified with $Y^i$ (index $m_i$ ↔ strategy $a^i_{m_i}$), so $m$ is a strategy profile. No potential property of $P$ is needed for this step.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 140–141 (PDF pp. 17–18), proof of Theorem 3.2, (B.2), (B.3) and the display at the top of p. 141

import Mathlib
import Definitions.Def_MondererShapley_Congestion_FacilityConstruction

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 141 (proof of Theorem 3.2): on the facility set
`M = ×_{i} {0,1}^{K(i)}`, for every `m ∈ K`,
`A¹_{m₁} ∩ A²_{m₂} ∩ ⋯ ∩ Aⁿ_{mₙ} ∩ M₁ = {ε(m)}`; therefore the vector `xⁿ` satisfies (B.2):
`xⁿ(A¹_{m₁} ∩ ⋯ ∩ Aⁿ_{mₙ}) = P(a¹_{m₁}, …, aⁿ_{mₙ})`.

**Formalization Note.** `K(i)` is identified with `Yⁱ` (`m_i` ↔ `aⁱ_{m_i}`), so `m` is a profile;
`x(B) = Σ_{j∈B} x(j)` is `vecSum`. -/
theorem eq_B_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (P : (∀ i, Y i) → ℝ) (m : ∀ i, Y i) :
    (⋂ i, stratFac i (m i)) ∩ M1 Y = {epsOf m} ∧
      vecSum (xn P) (⋂ i, stratFac i (m i)) = P m := by sorry

end MondererShapley.Congestion
