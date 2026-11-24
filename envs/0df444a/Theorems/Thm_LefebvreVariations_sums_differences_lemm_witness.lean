-- Prove2me | Theorems.Thm_LefebvreVariations_sums_differences_lemm_witness
-- name    : LefebvreVariations.sums_differences_lemm_witness
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:49:01.34421+00:00
-- url     : https://prove2.me/theorems/f908473a-a1ea-4203-985e-31880288356e
-- title:
--   Lefebvre's variations: a finite witness that $|A-_GB|$ can exceed $\max(|A|,|B|,|A+_GB|)^{1.77898}$ (Lemm's sums–differences counterexample)
-- statement:
--   For a finite set $G \subset \mathbb{Z}^2$ write
--   $$
--   A = \{a : (a,b) \in G\},\qquad B = \{b : (a,b)\in G\},\qquad A +_G B = \{a+b : (a,b) \in G\},\qquad A -_G B = \{a-b : (a,b)\in G\}.
--   $$
--   There exists a finite set $G \subset \mathbb{Z}^2$ such that
--   $$
--   |A -_G B|^{50000} \;>\; \max\bigl(|A|,\ |B|,\ |A +_G B|\bigr)^{88949},
--   $$
--   that is, $|A -_G B| > \max(|A|,|B|,|A+_G B|)^{1.77898}$.
--
--   This is a single finite witness of Lemm's theorem that the sums–differences inequality $\mathrm{SD}(0,1,\infty;\alpha)$, namely $|A -_G B| \lesssim \max(|A|,|B|,|A+_G B|)^{\alpha}$, fails for some $\alpha > 1.77898$: applying the failure of $\mathrm{SD}(\alpha)$ with constant $1$ gives a graph $G$ with $|A-_G B| > N^{\alpha} \ge N^{1.77898}$, where $N = \max(|A|,|B|,|A+_GB|)$, and replacing $A$, $B$ by the projections of $G$ only decreases $N$. Small sets cannot work: the best exponents $\log|A-_GB|/\log N$ for $N \le 6$ are about $1.63$ to $1.67$ (Ruzsa's $\log 6/\log 3$ at $N=3$), so a witness must come from a large construction such as a tensor power.
--
--   **Formalization Note** The set $G$ is a `Finset (ℤ × ℤ)`. $|A|$, $|B|$, $|A+_GB|$, $|A-_GB|$ are the cardinalities of the images of $G$ under `Prod.fst`, `Prod.snd`, `g ↦ g.1 + g.2` and `g ↦ g.1 - g.2`. The exponent $1.77898 = 88949/50000$ is cleared into natural-number powers, so the statement is a strict inequality in `ℕ`. Working in $\mathbb{Z}$ loses nothing: a finite configuration in a torsion-free group (or in $\mathbb{R}$) maps to $\mathbb{Z}$ by a Freiman isomorphism that preserves all four sets.
-- source:
--   M. Lemm, New counterexamples for sums-differences, Proc. Amer. Math. Soc. 143 (2015), 3863–3868 (failure of SD(0,1,∞;α) for some α > 1.77898; bibliographic details to be checked against the mission source). Background: N. H. Katz, T. Tao, Bounds on arithmetic projections, and applications to the Kakeya conjecture, Math. Res. Lett. 6 (1999) 625–630; I. Z. Ruzsa's earlier counterexample with exponent log 6 / log 3. Origin of this statement: it is the missing step of a reduction of ArithmeticKakeya.lemm_sums_differences_barrier (open milestone of the mission ArithmeticKakeya.arithmetic_kakeya_1675). The reduction, verified in Lean, proves that every forcing constructible proof for X = {(1,0),(0,1),(1,1)} satisfies |S|^(n-t) ≤ N^(m+r) for every finite S ⊂ ℤ² with injective differences and |x·S| ≤ N (graph counting lemma via a log-concavity chain bound, plus injectivity of the forcing map), and applies it to a section of the difference map inside the witness G.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem sums_differences_lemm_witness :
    ∃ G : Finset (ℤ × ℤ),
      (max (max (G.image Prod.fst).card (G.image Prod.snd).card)
          (G.image (fun g => g.1 + g.2)).card) ^ 88949 <
        (G.image (fun g => g.1 - g.2)).card ^ 50000 := by sorry
end LefebvreVariations
