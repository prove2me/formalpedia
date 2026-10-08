-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_chernoff_over_S
-- name    : ObfImpossibility.PseudoOracle.chernoff_over_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:21.718913+00:00
-- url     : https://prove2.me/theorems/538624c6-0051-459d-9fa6-39a74849d58f
-- title:
--   Proof of Claim B.1.1, p. A:43 — a random $S$ of size $K^{1-5\delta}$ estimates $\Pr_{x\in[K]}[D^G(G(x))=1]$ within $1/(4K^\delta)$
-- statement:
--   For every $0<\delta\le1/100$ there are a constant $c>0$ and a threshold $K_0$ such that the following holds for all $K\ge K_0$, all $L$, every distinguisher $D$ and every injective $G:[K]\to[L]$. Let $S$ be a uniformly random subset of $[K]$ of size $\lfloor K^{1-5\delta}\rfloor$, and let $p$ be the probability over $S$ that
--   $$\Big|\Pr_{x\in S}\big[D^G(G(x))=1\big]-\Pr_{x\in[K]}\big[D^G(G(x))=1\big]\Big|\le\frac{1}{4K^\delta}.$$
--   Then
--   $$p\ \ge\ 1-\exp\!\big(-c\,K^{1-5\delta}\,(K^{-\delta})^2\big)\qquad\text{and}\qquad p>\frac34 .$$
--
--   This is the sampling step behind Property 3 of Claim B.1.1: a random set of $K^{1-5\delta}$ inputs estimates the acceptance probability of $D$ on $G(x)$, $x\in[K]$, to within $1/(4K^\delta)$. The paper prints the exponent as $\exp(\Omega(\cdot))$; the minus sign is restored.
--
--   **Formalization Note** $\Omega(\cdot)$ is rendered as an explicit constant $c>0$ that may depend on $\delta$ but not on $K$, $L$, $D$ or $G$. Probabilities over $S$ are counting fractions over the $\binom{K}{s}$ subsets of size $s=\lfloor K^{1-5\delta}\rfloor$. The query bound on $D$ is not needed for this step and is not assumed.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:43, Appendix B, proof of Claim B.1.1 (Property 3, Chernoff-like bound)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- Proof of Claim B.1.1, p. A:43 (Property 3), the Chernoff-like bound: for every `D`
and `G`, with probability at least `1 - exp(-Ω(K^{1-5δ}·(K^{-δ})²)) > 3/4` over a
uniformly random `S ⊆ [K]` of size `⌊K^{1-5δ}⌋`,
`|Pr_{x∈S}[D^G(G(x)) = 1] - Pr_{x∈[K]}[D^G(G(x)) = 1]| ≤ 1/(4K^δ)`. -/
theorem chernoff_over_S :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K →
      ∀ (D : Fin L → QTree K L) (G : Fin K ↪ Fin L),
        1 - Real.exp (-(c * ((K : ℝ) ^ (1 - 5 * δ) * ((K : ℝ) ^ (-δ)) ^ 2))) ≤
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => |avg S (fun x => (D (G x)).run G) - prX D G| ≤
                  1 / (4 * (K : ℝ) ^ δ)).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) ∧
          (3 / 4 : ℝ) <
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => |avg S (fun x => (D (G x)).run G) - prX D G| ≤
                  1 / (4 * (K : ℝ) ^ δ)).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) := by sorry

end ObfImpossibility.PseudoOracle
