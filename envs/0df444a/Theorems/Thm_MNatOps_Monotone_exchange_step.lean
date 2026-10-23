-- Prove2me | Theorems.Thm_MNatOps_Monotone_exchange_step
-- name    : MNatOps.Monotone.exchange_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:12.627786+00:00
-- url     : https://prove2.me/theorems/d41a88de-c898-429a-8dce-c17554298529
-- title:
--   Proof of Theorem 3, p. 11 — exchange step: a′ − (eᵢ − eⱼ) ∈ A*_B(s′) ∩ I_{≤,i−1}(a) and a + (eᵢ − eⱼ) ∈ A*_B(s)
-- statement:
--   Let $G : \mathbb Z^m \times \mathbb Z^n \to \mathbb R \cup \{-\infty\}$ be SSQM♮-concave, let $B = [l, u] \cap \mathbb Z^n$ be a box, and let $s \le s'$ be parameters. Let $a \in \mathcal A^*_B(s)$ and $a' \in \mathcal A^*_B(s')$ be optimal solutions of problem (3) with finite values $G(s, a) > -\infty$ and $G(s', a') > -\infty$, and let $i$ be a coordinate with $a_i < a'_i$. Then there is $j$, either $0$ (with $\mathbf e_0 = 0$) or a coordinate with $a'_j < a_j$, such that
--   $$
--   a' - (\mathbf e_i - \mathbf e_j) \in \mathcal A^*_B(s'), \qquad a + (\mathbf e_i - \mathbf e_j) \in \mathcal A^*_B(s),
--   $$
--   and moreover, if $a' \in I_{\le, i-1}(a)$ (that is, $a'_k \le a_k$ for $k = 1, \dots, i - 1$), then also $a' - (\mathbf e_i - \mathbf e_j) \in I_{\le, i-1}(a)$.
--
--   This is the exchange step of the proof of Theorem 3, where SSQM♮-concavity is applied at the joint points $(s', a')$ and $(s, a)$.
--
--   **Formalization Note** Coordinates are `Fin n`, so the paper's coordinate $i$ is the index with value $i - 1$, and $I_{\le, i-1}(a)$ is `lowerOrthant a i.val`. Over $\mathbb Z$ "small $\alpha$" is $\alpha = 1$. The finiteness of $G(s,a)$ and $G(s',a')$ is the standing hypothesis of the mission (Theorem 3 is restricted to finite optimal values); it is what places the two joint points in $\operatorname{dom} G$.
-- source:
--   Chen & Li, M♮-Convexity and Its Applications in Operations, SSRN 3431474 (PDF sha256 ea81b5d5…), p. 11, proof of Theorem 3, 'Note that a′ⱼ < aⱼ implies … a′ − α(eᵢ − eⱼ) ∈ A*_B(s′) ∩ I≤,i−1 and a + α(eᵢ − eⱼ) ∈ A*_B(s).'

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model

namespace MNatOps.Monotone

theorem exchange_step {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (a : Fin n → ℤ) (ha : a ∈ optSet G l u s) (haf : G (Sum.elim s a) ≠ ⊥)
    (a' : Fin n → ℤ) (ha' : a' ∈ optSet G l u s') (ha'f : G (Sum.elim s' a') ≠ ⊥)
    (i : Fin n) (hi : a i < a' i) :
    ∃ j : Option (Fin n), (∀ k, j = some k → a' k < a k) ∧
      a' - dir i j ∈ optSet G l u s' ∧ a + dir i j ∈ optSet G l u s ∧
      (a' ∈ lowerOrthant a i.val → a' - dir i j ∈ lowerOrthant a i.val) := by sorry

end MNatOps.Monotone
