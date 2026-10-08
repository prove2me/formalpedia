-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_theorem_1
-- name    : GoldfarbIdnani.DualQP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:56.809331+00:00
-- url     : https://prove2.me/theorems/614fdc6c-35a3-493a-8f57-aeecd14dcd06
-- title:
--   Theorem 1 (pp. 8–9) — the step $t = \min\{t_1, t_2\}$ from a V-triple gives a V-triple or an S-pair
-- statement:
--   Let $G$ be symmetric positive definite and let $(x, A, p)$ be a V-triple for (1.1), with $n^+ = n_p$, $z = Hn^+$, $r = N^*n^+$ and $u^+ = u^+(x) = (N^+)^*g(x)$. Define
--
--   $$
--   t_1 = \min\Bigl\{\min_{j \in A,\ r_j > 0} \frac{u^+_j}{r_j},\ \infty\Bigr\}, \qquad t_2 = -\frac{s_p(x)}{z^{\mathsf T}n^+}, \qquad t = \min\{t_1, t_2\},
--   $$
--
--   and $\bar x = x + tz$. Then
--
--   1. $s_p(\bar x) \ge s_p(x)$; (3.15)
--   2. $f(\bar x) - f(x) = t\,z^{\mathsf T}n^+\bigl(\tfrac12t + u^+_p\bigr) \ge 0$; (3.16)
--   3. if $t = u^+_k/r_k$ for some $k \in A$ with $r_k > 0$, and $t < t_2$, then $(\bar x, A \setminus \{k\}, p)$ is a V-triple;
--   4. if $t = t_2$, then $(\bar x, A \cup \{p\})$ is an S-pair.
--
--   This is the core step of the method: from a V-triple, either a full step reaches a new S-pair with the violated constraint $p$ added, or a partial step drops one active constraint and leaves a V-triple, and the objective never decreases.
--
--   **Formalization Note.** For a V-triple, $z \ne 0$ and $z^{\mathsf T}n^+ > 0$, so $t_2$ is a finite real, while $t_1 \in \mathbb R \cup \{+\infty\}$ (`WithTop ℝ`); $t$ is the real number with $t = \min\{t_1, t_2\}$. The paper prints the multiplier in (3.16) as $u^+_{j+1}(x)$; it is the last component $u^+_{q+1}(x)$, the entry belonging to $p$ (as in the proof, (3.19)). The paper's partial-step clause reads "if $t = t_1 = u_l^+(x)/r_l$"; it is stated here with $t < t_2$, as the proof does ("If $t = t_1 < t_2$"): at a tie $t_1 = t_2$ one has $s_p(\bar x) = 0$, (3.1) fails, and the full-step clause applies.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), pp. 8–9, Theorem 1, Eqs. (3.12)–(3.16)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

theorem theorem_1 {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (t : ℝ)
    (hG : G.PosDef) (hV : IsVTriple a G C b x A p)
    (ht : (t : WithTop ℝ) =
      min (t1 A (multVec G C (insert p A) (grad a G x)) (multVec G C A (normal C p)))
        ((-slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p) : ℝ) : WithTop ℝ)) :
    let z := Hmat G C A *ᵥ normal C p
    let r := multVec G C A (normal C p)
    let uplus := multVec G C (insert p A) (grad a G x)
    let t2 := -slack C b x p / (z ⬝ᵥ normal C p)
    let xbar := x + t • z
    slack C b x p ≤ slack C b xbar p ∧
    f a G xbar - f a G x = t * (z ⬝ᵥ normal C p) * ((1 / 2 : ℝ) * t + uplus p) ∧
    0 ≤ t * (z ⬝ᵥ normal C p) * ((1 / 2 : ℝ) * t + uplus p) ∧
    (∀ k ∈ A, 0 < r k → t = uplus k / r k → t < t2 → IsVTriple a G C b xbar (A.erase k) p) ∧
    (t = t2 → IsSPair a G C b xbar (insert p A)) := by sorry

end GoldfarbIdnani.DualQP
