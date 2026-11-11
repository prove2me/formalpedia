-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_6_1
-- name    : MarginMaxima.Critical.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:42.981422+00:00
-- url     : https://prove2.me/theorems/e60f2a36-0d5e-4b25-8679-a5dc9557f167
-- title:
--   Lemma 6.1 — $q$-ary lines: agreement $L$ on the line, $\le (q^{t-1}-1)/(q-1)\le L/q$ off it; lines through $x$ meet only at $x$; lines of one direction partition $C$
-- statement:
--   In the setting of §6 ($q$ a prime power, $t\ge2$, $e\ge1$, $C=\mathbb F_q^{t\times e}$, $A$ a set of representatives of the nonzero $a\in\mathbb F_q^t$ modulo scalars, $L=|A|$), for $x\in C$ and nonzero $\beta\in\mathbb F_q^e$:
--
--   (i) $A(Y)=L$ on the line $B(x,\beta)$, and $A(Y)\le(q^{t-1}-1)/(q-1)\le L/q$ off the line.
--
--   (ii) Lines through $x$ with non-proportional $\beta$ meet only at $x$.
--
--   (iii) For fixed $\beta$ the lines partition $C$. There are $(q^e-1)/(q-1)$ classes of $\beta$.
--
--   Differences from the source:
--   - encoding: q a prime power, F_q → any finite field F, q = Fintype.card F; reason: every finite field has prime-power order and fields of equal order are isomorphic
--   - encoding: A a set of representatives, L = |A| → any A with IsProjReps A; L written A.card; reason: the lemma holds for every choice of representatives
--   - encoding: non-proportional β, β′ (both nonzero) → β ≠ 0, β′ ≠ 0 and ¬∃ c, β′ = c • β; reason: for nonzero vectors proportionality is symmetric
--   - encoding: for fixed β the lines partition C; there are (q^e − 1)/(q − 1) classes of β → Setoid.IsPartition (range fun x => qLine x β); every set of representatives of nonzero β modulo scalars has (q^e − 1)/(q − 1) elements; reason: literal: a class of β is a projective point of F_q^e
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 13, Lemma 6.1

import Mathlib
import Definitions.Def_MarginMaxima_Critical_QaryGadget

namespace MarginMaxima.Critical

theorem lemma_6_1 {F : Type} [Field F] [Fintype F] [DecidableEq F] (t e : ℕ) (ht : 2 ≤ t)
    (he : 1 ≤ e) (A : Finset (Fin t → F)) (hA : IsProjReps A) :
    (∀ (x : Matrix (Fin t) (Fin e) F) (β : Fin e → F), β ≠ 0 →
        (∀ Y ∈ qLine x β, qAgree A x β Y = A.card) ∧
        (∀ Y ∉ qLine x β,
          (qAgree A x β Y : ℝ) ≤ ((Fintype.card F : ℝ) ^ (t - 1) - 1) / (Fintype.card F - 1) ∧
          ((Fintype.card F : ℝ) ^ (t - 1) - 1) / (Fintype.card F - 1) ≤
            (A.card : ℝ) / Fintype.card F)) ∧
      (∀ (x : Matrix (Fin t) (Fin e) F) (β β' : Fin e → F), β ≠ 0 → β' ≠ 0 →
        (¬ ∃ c : F, β' = c • β) → qLine x β ∩ qLine x β' = {x}) ∧
      (∀ β : Fin e → F, β ≠ 0 → Setoid.IsPartition (Set.range fun x : Matrix (Fin t) (Fin e) F => qLine x β)) ∧
      (∀ Bs : Finset (Fin e → F), IsProjReps Bs →
        (Bs.card : ℝ) = ((Fintype.card F : ℝ) ^ e - 1) / (Fintype.card F - 1)) := by sorry

end MarginMaxima.Critical
