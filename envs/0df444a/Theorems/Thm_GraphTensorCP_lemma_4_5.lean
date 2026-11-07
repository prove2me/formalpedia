-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_4_5
-- name    : GraphTensorCP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:55.178568+00:00
-- url     : https://prove2.me/theorems/c8e1bf1f-f3a5-44c2-b731-c275564d6bbe
-- title:
--   Lemma 4.5 — discrete concavity $2P_\phi(\dots,b)\ge P_\phi(\dots,b+1)+P_\phi(\dots,b-1)$ in every coordinate
-- statement:
--   For every integer $n\ge3$, every $\phi\in\Phi_{n,\mathbb F}$, all positive integers $a_1,\dots,a_{n-2}$ and every integer $b\ge2$,
--
--   $$2P_\phi(a_1,\dots,a_{n-2},b)\ge P_\phi(a_1,\dots,a_{n-2},b+1)+P_\phi(a_1,\dots,a_{n-2},b-1).$$
--
--   The same inequality holds in every input coordinate: for every coordinate $j$, with the other arguments fixed positive integers, $b\mapsto P_\phi(\dots,b,\dots)$ is discretely concave on $b\ge1$.
--
--   **Formalization Note** The statement is given for every coordinate $j\in\mathrm{Fin}(n-1)$ at once: coordinate $j$ of a positive tuple $a$ is replaced by $b$, $b+1$, $b-1$ (`Function.update`); $j=n-2$ is the displayed case.
--
--   Differences from the source:
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: the displayed inequality in the last argument, plus "the same inequality holds in every input coordinate" → one statement for every coordinate $j$ via `Function.update`; reason: the two clauses of the source are exactly the cases $j=n-2$ and general $j$
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 4.5, p.39

import Mathlib
import Definitions.Def_GraphTensorCP_profile

universe u

namespace GraphTensorCP

/-- **Lemma 4.5** (discrete concavity), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.39:
"For every integer n ≥ 3, every ϕ ∈ Φ_{n,F}, all positive integers a₁, . . . , a_{n−2}, and every
integer b ≥ 2, 2P_ϕ(a₁, . . . , a_{n−2}, b) ≥ P_ϕ(a₁, . . . , a_{n−2}, b + 1) + P_ϕ(a₁, . . . , a_{n−2}, b − 1).
The same inequality holds in every input coordinate."

**Formalization Note.** Stated for every input coordinate `j : Fin (n−1)` at once: the other
arguments are the entries `a i` (`i ≠ j`) of a positive tuple `a`, and coordinate `j` is set to
`b`, `b + 1`, `b − 1` by `Function.update` (the value `a j` is overwritten). The case
`j = n − 2` is the displayed inequality. `hn : 1 < n` only types the spectrum. -/
theorem lemma_4_5 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (hn3 : 3 ≤ n) (φ : Spec K n hn) :
    ∀ (j : Fin (n - 1)) (a : Fin (n - 1) → ℕ), (∀ i, 0 < a i) → ∀ b : ℕ, 2 ≤ b →
      profile φ (Function.update a j (b + 1)) + profile φ (Function.update a j (b - 1)) ≤
        2 * profile φ (Function.update a j b) := by sorry

end GraphTensorCP
