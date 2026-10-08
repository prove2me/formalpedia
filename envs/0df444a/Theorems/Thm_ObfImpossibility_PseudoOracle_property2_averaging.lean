-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_property2_averaging
-- name    : ObfImpossibility.PseudoOracle.property2_averaging
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:26.634002+00:00
-- url     : https://prove2.me/theorems/66995e1b-617d-431c-b329-5043e8dbb573
-- title:
--   Proof of Claim B.1.1, p. A:43 — for most $S$ of size $K^{1-5\delta}$, at most a $4K^{-4\delta}$ fraction of $x\in S$ query $S\setminus\{x\}$ (corrected)
-- statement:
--   Let $0<\delta\le 1/100$, let $K,L$ be natural numbers, let $D$ be a distinguisher making at most $K^\delta$ oracle queries, and let $G:[K]\to[L]$ be injective. Put $s=\lfloor K^{1-5\delta}\rfloor$ and choose $S$ uniformly among the $s$-element subsets of $[K]$. Then
--   $$\Pr_S\Big[\ \#\{x\in S:\ D^G(G(x)) \text{ queries its oracle at an element of } S\setminus\{x\}\}\ \le\ 4K^{-4\delta}\,|S|\ \Big]\ \ge\ \frac34 .$$
--
--   This is the averaging step behind Property 2 of Claim B.1.1: since $D$ makes at most $K^\delta$ queries and $S$ has density about $K^{-5\delta}$, few $x\in S$ have runs that hit the rest of $S$, and discarding them leaves a large subset of $S$ that the remaining runs avoid.
--
--   The statement differs from the printed sentence in two ways. The paper writes "$4/K^{-4\delta}$", a misprint for $4K^{-4\delta}$. More importantly, the paper counts queries at *any* element of $S$, including $x$ itself; that version is false. A one-query distinguisher $D(y)$ that queries $h(y)$ and outputs $1$ iff the answer is $y$, where $h\circ G=\mathrm{id}$, queries $x$ on input $G(x)$ for every $x$, and every such $G$ violates (7). The bound here excludes the query at $x$ and holds for every $G$, hence also for $G$ drawn from the set of $G$ violating (7), as the paper uses it.
--
--   **Formalization Note** The probability is the number of good $S$ in `Finset.powersetCard s univ` divided by $\binom{K}{s}$. "Fraction of $x\in S$" is written multiplicatively, $\#\{\dots\}\le 4K^{-4\delta}|S|$, which is the same condition for $S\ne\emptyset$. The restriction $\delta\le1/100$ is the paper's "sufficiently small $\delta$" made explicit.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:43, Appendix B, proof of Claim B.1.1 (Property 2); corrected: excludes the query at x, reads 4/K^{−4δ} as 4K^{−4δ}

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- Proof of Claim B.1.1, p. A:43 (Property 2), corrected: for every `G`, with probability
at least `3/4` over a uniformly random `S ⊆ [K]` of size `⌊K^{1-5δ}⌋`, the run of
`D^G(G(x))` queries its oracle at an element of `S` other than `x` itself for at most a
`4K^{-4δ}` fraction of the `x ∈ S`. The paper prints `4/K^{-4δ}` and does not exclude the
query at `x`; the printed form is false (a one-query `D` that inverts `G` breaks it). -/
theorem property2_averaging :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ K L : ℕ,
      ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        ∀ G : Fin K ↪ Fin L,
          (3 / 4 : ℝ) ≤
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => (((S.filter fun x => (D (G x)).hits G (S.erase x) = true).card : ℝ) ≤
                  4 * (K : ℝ) ^ (-(4 * δ)) * (S.card : ℝ))).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) := by sorry

end ObfImpossibility.PseudoOracle
