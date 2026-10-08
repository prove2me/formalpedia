-- Prove2me | Theorems.Thm_ImpulseGames_LinearGame_lemma_4_6
-- name    : ImpulseGames.LinearGame.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:28:30.940967+00:00
-- url     : https://prove2.me/theorems/cdb71033-562b-40d0-b49d-ab5050eda32d
-- title:
--   Lemma 4.6: the optimal impulses (4.23) and the intervention regions $\{\mathcal M_i\tilde V_i-\tilde V_i<0\}$ (4.24)
-- statement:
--   Assume the standing assumptions of Section 4.1, $c>0$, let $\xi\in(0,\eta)$ be the zero of $F$, fix $\tilde s\in\mathbb R$, and let $\tilde V_1,\tilde V_2$ be as in Definition 4.1 with the parameters (4.20). Set
--   $$\delta_1(x)=\begin{cases}x_1^*-x,&x\in]-\infty,x_1^*],\\0,&x\in]x_1^*,+\infty[,\end{cases}\qquad \delta_2(x)=\begin{cases}0,&x\in]-\infty,x_2^*[,\\x_2^*-x,&x\in[x_2^*,+\infty[.\end{cases}\tag{4.23}$$
--   Then for every $x\in\mathbb R$:
--
--   1. $\delta_1(x)\ge0$ maximises $\delta\mapsto\tilde V_1(x+\delta)-c-\lambda|\delta|$ over $\delta\ge0$, and it is the only maximiser unless $\lambda=\tilde\lambda$ and $x\ge\bar x_2$;
--   2. $\delta_2(x)\le0$ maximises $\delta\mapsto\tilde V_2(x+\delta)-c-\lambda|\delta|$ over $\delta\le0$, and it is the only maximiser unless $\lambda=\tilde\lambda$ and $x\le\bar x_1$.
--
--   Moreover, with $\mathcal M_1\tilde V_1(x)=\sup_{\delta\ge0}\{\tilde V_1(x+\delta)-c-\lambda\delta\}$ and $\mathcal M_2\tilde V_2(x)=\sup_{\delta\le0}\{\tilde V_2(x+\delta)-c+\lambda\delta\}$,
--   $$\begin{aligned}&\mathcal M_1\tilde V_1-\tilde V_1\le0,\quad\{\mathcal M_1\tilde V_1-\tilde V_1<0\}=]\bar x_1,+\infty[,\quad\{\mathcal M_1\tilde V_1-\tilde V_1=0\}=]-\infty,\bar x_1],\\ &\mathcal M_2\tilde V_2-\tilde V_2\le0,\quad\{\mathcal M_2\tilde V_2-\tilde V_2<0\}=]-\infty,\bar x_2[,\quad\{\mathcal M_2\tilde V_2-\tilde V_2=0\}=[\bar x_2,+\infty[.\end{aligned}\tag{4.24}$$
--
--   Thus player 1 intervenes exactly below $\bar x_1$ and player 2 exactly above $\bar x_2$, each moving the state to $x_i^*$.
--
--   **Formalization Note.** The paper defines $\delta_i$ in (3.1) as the unique maximiser and states (4.23) for every $x$. When $\lambda=\tilde\lambda$ (allowed if $c>\tilde c$) uniqueness fails in the opponent's intervention region: for $x\le\bar x_1$, $\tilde V_2(x+\delta)-c-\lambda|\delta|=\varphi_2(x_1^*)+\tilde c+\tilde\lambda(x_1^*-x)-c+(\lambda-\tilde\lambda)\delta$ is constant in $\delta\le0$ (symmetrically for player 1 at $x\ge\bar x_2$); the proof's "$\Gamma_2'=\lambda-\tilde\lambda\ge0$" overlooks this. The statement asserts maximality everywhere and uniqueness outside that tie region. The suprema are real `sSup`s; the maximiser part shows that they are attained.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Lemma 4.6 (p. 17), with (3.1)-(3.2) (p. 7)

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Candidates

namespace ImpulseGames.LinearGame

/-- Lemma 4.6 (p. 17): for the candidates `Ṽ₁, Ṽ₂` of Definition 4.1 built on (4.20), the
functions `δ₁, δ₂` of (4.23) maximise `δ ↦ Ṽᵢ(x + δ) − c − λ|δ|` over `Zᵢ` (3.1), uniquely except
in the tie region that occurs when `λ = λ̃` (player 1 at `x ≥ x̄₂`, player 2 at `x ≤ x̄₁`), and
the intervention regions are described by (4.24). -/
theorem lemma_4_6 (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) :
    -- (4.23): δ₁(x) is a maximiser over Z₁ = [0, ∞[, the unique one unless λ = λ̃ and x ≥ x̄₂
    (∀ x : ℝ, 0 ≤ delta1 M ξ s x ∧
      ∀ δ : ℝ, 0 ≤ δ →
        Vt1 M ξ s (x + δ) - M.c - M.lam * |δ| ≤
          Vt1 M ξ s (x + delta1 M ξ s x) - M.c - M.lam * |delta1 M ξ s x| ∧
        ((M.lamt < M.lam ∨ x < xbar M ξ s 2) →
          Vt1 M ξ s (x + δ) - M.c - M.lam * |δ| =
          Vt1 M ξ s (x + delta1 M ξ s x) - M.c - M.lam * |delta1 M ξ s x| →
            δ = delta1 M ξ s x)) ∧
    -- (4.23): δ₂(x) is a maximiser over Z₂ = ]−∞, 0], the unique one unless λ = λ̃ and x ≤ x̄₁
    (∀ x : ℝ, delta2 M ξ s x ≤ 0 ∧
      ∀ δ : ℝ, δ ≤ 0 →
        Vt2 M ξ s (x + δ) - M.c - M.lam * |δ| ≤
          Vt2 M ξ s (x + delta2 M ξ s x) - M.c - M.lam * |delta2 M ξ s x| ∧
        ((M.lamt < M.lam ∨ xbar M ξ s 1 < x) →
          Vt2 M ξ s (x + δ) - M.c - M.lam * |δ| =
          Vt2 M ξ s (x + delta2 M ξ s x) - M.c - M.lam * |delta2 M ξ s x| →
            δ = delta2 M ξ s x)) ∧
    -- (4.24), player 1
    (∀ x : ℝ, M1op M (Vt1 M ξ s) x - Vt1 M ξ s x ≤ 0) ∧
    {x : ℝ | M1op M (Vt1 M ξ s) x - Vt1 M ξ s x < 0} = Set.Ioi (xbar M ξ s 1) ∧
    {x : ℝ | M1op M (Vt1 M ξ s) x - Vt1 M ξ s x = 0} = Set.Iic (xbar M ξ s 1) ∧
    -- (4.24), player 2
    (∀ x : ℝ, M2op M (Vt2 M ξ s) x - Vt2 M ξ s x ≤ 0) ∧
    {x : ℝ | M2op M (Vt2 M ξ s) x - Vt2 M ξ s x < 0} = Set.Iio (xbar M ξ s 2) ∧
    {x : ℝ | M2op M (Vt2 M ξ s) x - Vt2 M ξ s x = 0} = Set.Ici (xbar M ξ s 2) := by sorry

end ImpulseGames.LinearGame
