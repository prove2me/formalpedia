-- Prove2me | Theorems.Thm_GeneralCK_mostInformativeBooleanFunction
-- name    : GeneralCK.mostInformativeBooleanFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T15:49:44.461609+00:00
-- url     : https://prove2.me/theorems/bde405e1-4a4d-49b9-8e4e-f741842d6f8f
-- title:
--   Most Informative Boolean Function conjecture (general Courtade-Kumar inequality)
-- statement:
--   **The general Courtade–Kumar inequality (Most Informative Boolean Function conjecture).** Let $X$ be uniformly distributed on the Boolean cube $\{0,1\}^n$ and let $Y$ be the output of a memoryless binary symmetric channel applied to $X$, i.e. each coordinate of $X$ is flipped independently with crossover probability $p \in [0,1]$. Then for **every** $n \in \mathbb{N}$ and **every** Boolean function $f : \{0,1\}^n \to \{0,1\}$,
--   $$I\bigl(f(X);\,Y\bigr) \;\le\; 1 - H(p),$$
--   where $H$ is the binary entropy function in bits, $H(p) = h_2(p)$ with $H(1/2) = 1$.
--
--   The bound is tight and is attained by a dictator function $f(x) = x_i$: then $f(X)$ is a uniform bit, $I(f(X); Y) = I(X_i; Y_i) = 1 - H(p)$. The content of the theorem is that no Boolean function of the $n$ input bits — however many bits it depends on, and however cleverly it combines them — extracts more information about the noisy observation $Y$ than a single coordinate does. Equivalently, dictators are the most informative Boolean functions.
--
--   Conjectured by Courtade and Kumar (2014) and open for a decade, it is proved in Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair and D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). The formal statement here is the `GeneralCK.GeneralCourtadeKumar` proposition of the accompanying definition module: all dimensions including $n = 0$, all Boolean functions, and all crossover probabilities including the endpoints $p \in \{0, 1/2, 1\}$. Mutual information and entropy are defined by explicit finite sums over the cube, in bits, so the statement needs no measure theory.
--
--   A complete machine-checked Lean 4 proof exists (Lean 4.33.0, Mathlib `db584cd6`; axioms `[propext, Classical.choice, Quot.sound]`, no `sorry` and no `native_decide`), but it spans 45,500 modules and roughly 50 million lines of kernel-checked certificate data, so it cannot be submitted here as a single solution: it has to be transplanted onto the platform as a dependency graph of nodes. This node is the root of that graph.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/b821c742246c47508fb5d85b283c4760799f995f/final/Final.lean#L26-L47 (GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed); statement: browse/GeneralCK/Statement.lean#L1-L63; paper: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026), Theorem 1.1

import Definitions.Def_GeneralCK_statement

theorem GeneralCK.mostInformativeBooleanFunction : GeneralCK.GeneralCourtadeKumar := by sorry
