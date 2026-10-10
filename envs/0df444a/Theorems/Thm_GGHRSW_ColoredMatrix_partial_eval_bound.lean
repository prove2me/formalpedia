-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_partial_eval_bound
-- name    : GGHRSW.ColoredMatrix.partial_eval_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:33.893996+00:00
-- url     : https://prove2.me/theorems/9702ddb0-324f-4211-be54-80960b5f5e90
-- title:
--   Proof of Theorem 6, §C.3.1, p. 41 — two distinct partial-evaluation polynomials in the D_{i,b} collide with probability ≤ (length)/p
-- statement:
--   Let $p$ be prime, $L\ge0$ and $r\ge1$. For each step $k=1,\dots,L$ and bit $b$ fix an arbitrary $5\times5$ matrix $B_{k,b}$ over $\mathbb Z_p$, and let
--   $$D_{k,b} = \begin{pmatrix} \operatorname{diag}(d_{k,b}) & 0\\ 0 & B_{k,b}\end{pmatrix}$$
--   where the diagonal entries $d_{k,b}\in\mathbb Z_p^r$ are drawn independently and uniformly. Let $f,g:\{0,1\}^L\to\mathbb Z_p$ be two different coefficient functions and consider the formal multilinear polynomials
--   $$P = \sum_{\mathbf b} f(\mathbf b)\, D_{1,b_1}\cdots D_{L,b_L},\qquad P' = \sum_{\mathbf b} g(\mathbf b)\, D_{1,b_1}\cdots D_{L,b_L}.$$
--   Then
--   $$\Pr_{d}\big[P = P' \text{ as matrices over } \mathbb Z_p\big] \le \frac{L}{p}.$$
--
--   In the proof of Theorem 6 this is the case of a "partial evaluation" query with colours $LC=i>0$ and $RC=j<n+2$: the new matrix and an earlier one have the form $R_{i-1}DR_{j-1}^{-1}$ with the same invertible $R$'s, so they coincide iff $c\cdot D=c_k\cdot D_k$, and the segment has $L=j-i\le n$ steps, giving the page's bound $n/p$.
--
--   **Formalization Note.** The page writes each polynomial as one scalar times one matrix $c\cdot D$ and calls the earlier polynomial $P_k$; its $D$ is a linear combination of products of the $D_{k,b}$, which is the sum with coefficients $f$ above. The conjugation by $R_{i-1}$ and $R_{j-1}^{-1}$ is dropped because it is invertible (the page's own "equal if and only if"); the page's $R_j^{-1}$ is read as $R_{j-1}^{-1}$, the right randomizer of a product ending at colour $j$. Fixed steps are the special case where $f$, $g$ vanish off the allowed bit. The bottom-right blocks $B_{k,b}$ are arbitrary (in the scheme they are $\alpha_{k,b}A_{k,b}$), and the bound is stated as $L/p$, which is at most $n/p$.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 41, proof of Theorem 6, §C.3.1, case LC = i > 0 and RC = j < n + 2

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

open Classical

namespace GGHRSW.ColoredMatrix

theorem partial_eval_bound (p : ℕ) [Fact p.Prime] (L r : ℕ) (hr : 0 < r)
    (B : Fin L → Bool → Matrix (Fin 5) (Fin 5) (ZMod p))
    (f g : (Fin L → Bool) → ZMod p) (hfg : f ≠ g) :
    ((Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
        ∑ b : Fin L → Bool, f b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod =
          ∑ b : Fin L → Bool, g b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod).card
        : ℝ) / Fintype.card (Fin L → Bool → Fin r → ZMod p) ≤ (L : ℝ) / p := by sorry

end GGHRSW.ColoredMatrix
