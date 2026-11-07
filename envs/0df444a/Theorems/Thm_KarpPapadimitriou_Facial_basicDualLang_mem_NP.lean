-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_basicDualLang_mem_NP
-- name    : KarpPapadimitriou.Facial.basicDualLang_mem_NP
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T01:01:38.570607+00:00
-- url     : https://prove2.me/theorems/668ed80a-900e-4b95-9f6a-c307bcd5aac3
-- title:
--   Theorem 1, proof (p. 8) — condition (vi) is checkable in NP
-- statement:
--   Let $C=(L,n,S)$ be a combinatorial optimization problem and let $F(C)$ be a small facial description of $C$ such that $F(C)\in\mathrm{NP}$ (the language of codes $\langle z,f,g\rangle$ of its triples is in NP).
--
--   Let $V(C)$ be the language of all strings $w$ over the alphabet $\{0,1,-,\#\}$ with the following property: whenever $w=\langle z,c,k\rangle$ with $z\in L$, $c\in\mathbb Z^{n(z)}$, $k\in\mathbb Z$, and $S(z)\neq\emptyset$, condition (vi) of the proof of Theorem 1 holds, namely there are an integer $n(z)\times n(z)$ matrix $(f_{ij})$ with $\det(f_{ij})\neq 0$ and an integer vector $g$ such that
--   $$\langle z,(f_{i1},\dots,f_{in(z)}),g_i\rangle\in F(C)\quad(i=1,\dots,n(z)),$$
--   and the system $y^{T}F=c$ has a (necessarily unique) nonnegative rational solution $y$ with
--   $$y^{T}g<k.$$
--   (Strings that encode no such triple, and triples with $S(z)=\emptyset$, belong to $V(C)$ vacuously.) Then
--   $$V(C)\in\mathrm{NP}.$$
--
--   This is the complexity half of the proof of Theorem 1 of Karp and Papadimitriou (the assertion that condition (vi) can be checked in NP). Combined with the equivalences (i)$\Leftrightarrow$(vi) of that proof, it yields $D(C)\in$ co-NP.
--
--   **Formalization Note** P and NP are Cook's classes over the alphabet $\{0,1,-,\#\}$ with integers in binary. Uniqueness of $y$ is expressed by $\det(f_{ij})\neq0$. For strings that are not codes, or codes with $S(z)=\emptyset$, membership is automatic; a proof must therefore also certify, in NP, that a string is not a well-formed code with $z\in L$, and (using the facial description) that $S(z)=\emptyset$.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 8, proof of Theorem 1, condition (vi) and the concluding NP-checkability argument

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

theorem basicDualLang_mem_NP (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (hNP : tripleLang C F ∈ NP BSym) :
    {w : List BSym | ∀ z ∈ C.L, ∀ (c : Fin (C.n z) → ℤ) (k : ℤ), w = encTriple z c k →
        (C.S z).Nonempty →
        ∃ (fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ) (g : Fin (C.n z) → ℤ),
          (∀ i, (⟨z, (fm i, g i)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F) ∧
            fm.det ≠ 0 ∧
            ∃ y : Fin (C.n z) → ℚ,
              Matrix.vecMul y (fm.map (fun a : ℤ => (a : ℚ))) = (fun j => (c j : ℚ)) ∧
                0 ≤ y ∧ y ⬝ᵥ (fun i => (g i : ℚ)) < (k : ℚ)} ∈ NP BSym := by sorry

end KarpPapadimitriou.Facial
