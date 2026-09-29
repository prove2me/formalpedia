-- Prove2me | Theorems.Thm_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
-- name    : LocalNewvector.indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8a9f44e6-4c8a-5cce-9b7f-b1747ab50420
-- title:
--   Indicator of B· K(p^M) lies in a translation-stable space
-- statement:
--   Let $p$ be a prime and let $S$ be a $\mathbb C$-submodule of the space of all functions $\mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ which is stable under right translation, i.e. for every $h \in \mathrm{GL}_2(\mathbb Q_p)$ and every $F \in S$ the function $g \mapsto F(gh)$ again lies in $S$. Let $\Phi : \mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ be a member of $S$ subject to: (i) $\Phi(bg) = \Phi(g)$ for all $g$ and all invertible $b$ whose lower-left entry $b_{10}$ vanishes, i.e. left invariance under the Borel subgroup of upper triangular matrices; (ii) for some integer $L \ge 1$, $\Phi(\,\cdot\,m) = \Phi$ for every $m$ in the level-$p^L$ congruence subgroup [`FLT.SmoothVectors.gl2CongruenceSubgroup p L`](def/RepTheory_GL2CongruenceSubgroup.html#L181), consisting of those $m$ for which all entries of $m - 1$ and of $m^{-1} - 1$ have norm at most $p^{-L}$; (iii) $\Phi(\,\cdot\,u) = \Phi$ for $u = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ with $\|x\| \le 1$; (iv) $\Phi(\,\cdot\,t) = \Phi$ for $t = \begin{pmatrix} a & 0 \\ 0 & 1\end{pmatrix}$ with $a \in \mathbb Q_p^{\times}$ of norm $1$ (both $u$ and $t$ being given by [`LocalNewvector.borelElem`](def/LocalNewvector_PrincipalSeriesCarrier.html#L13), the upper triangular unit with prescribed diagonal and upper-right entry); and (v) $\Phi$ is non-constant in the sense that $\Phi(g) \ne \Phi(1)$ for some $g$. Then for every integer $M \ge 2$ the function taking the value $1$ on $\{g : \|g_{10}\| \le p^{-M}\,\|g_{11}\|\}$ and $0$ elsewhere belongs to $S$.
--
--   On $B \backslash \mathrm{GL}_2(\mathbb Q_p) \cong \mathbb P^1(\mathbb Q_p)$ the hypotheses describe a non-constant function depending only on the distance to the base point, and the set $\{\|g_{10}\| \le p^{-M}\|g_{11}\|\}$ is the Borel cell $B \cdot K(p^M)$, a small ball around that base point; the conclusion is that the right translates of such a $\Phi$ generate the indicator functions of all these balls. It is the computational step in the elementary irreducibility argument for the Steinberg representation, and it is used by [`LocalNewvector.mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable`](thm.html#LocalNewvector.mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.lean

import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
    (p : ℕ) [Fact p.Prime] (S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ))
    (hS : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S)
    (Φ : GL (Fin 2) ℚ_[p] → ℂ) (hΦS : Φ ∈ S)
    (hΦB : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → Φ (b * g) = Φ g)
    {L : ℕ} (hL : 1 ≤ L)
    (hΦK : ∀ m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p L, (fun g => Φ (g * m)) = Φ)
    (hΦN : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → (fun g => Φ (g * LocalNewvector.borelElem p 1 1 x)) = Φ)
    (hΦT : ∀ a : ℚ_[p]ˣ, ‖(a : ℚ_[p])‖ = 1 →
      (fun g => Φ (g * LocalNewvector.borelElem p a 1 0)) = Φ)
    (hΦnc : ∃ g : GL (Fin 2) ℚ_[p], Φ g ≠ Φ 1) (M : ℕ) (hM : 2 ≤ M) :
    Set.indicator {g : GL (Fin 2) ℚ_[p] | ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖} 1 ∈ S := by sorry
