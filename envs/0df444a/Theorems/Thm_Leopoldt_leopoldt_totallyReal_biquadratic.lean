-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_totallyReal_biquadratic
-- name    : Leopoldt.leopoldt_totallyReal_biquadratic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:47:04.435538+00:00
-- url     : https://prove2.me/theorems/5d74aaeb-35b0-41cc-9196-f22668de5b47
-- title:
--   Leopoldt's conjecture for totally real biquadratic fields
-- statement:
--   Leopoldt's conjecture holds, at every prime $p$, for every totally real biquadratic field: if $\mathbb{K}$ is totally real, Galois over $\mathbb{Q}$ of degree $4$, and every element of $G = \mathrm{Gal}(\mathbb{K}/\mathbb{Q})$ satisfies $\sigma^2 = 1$ (so $G \cong (\mathbb{Z}/2)^2$ and $\mathbb{K} = \mathbb{Q}(\sqrt{a},\sqrt{b})$ with $a, b > 0$), then
--
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E}) \;=\; 0 .$$
--
--   Here $E = \mathcal{O}_{\mathbb{K}}^\times$ has $\mathbb{Z}$-rank $4 - 1 = 3$, and $\overline{E}$ is the $p$-adic closure of the diagonal image of $E$ in the semilocal units $U = \prod_{\mathfrak{P} \mid p} \mathcal{O}_{\mathfrak{P}}^\times$.
--
--   This is the unit-rank-$3$ case of Brumer's theorem (Leopoldt's conjecture for abelian fields), the first case beyond unit rank $1$ where the conjecture has genuine content for totally real fields. The units of the three real quadratic subfields $k_1, k_2, k_3$ generate a subgroup of finite index in $E$, and the Galois group acts on each of them through a distinct character; this eigenspace decomposition is what makes the biquadratic case accessible by elementary means, without Baker's theory of linear forms in $p$-adic logarithms.
--
--   **Formalization note.** "Biquadratic" is spelled as `IsGalois ℚ K`, $[\mathbb{K}:\mathbb{Q}] = 4$ and `∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1`, and "totally real" as `IsTotallyReal K`. No hypothesis on $p$ beyond primality is needed. In particular $p = 2$ is allowed.
-- source:
--   A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124 (Leopoldt's conjecture for abelian extensions of Q, via Baker's theorem); for the elementary argument in the biquadratic case via the decomposition 2 = (1+s1)+(1+s2)+(1+s3)-(1+s1+s2+s3) in Z[G] and the eigen-behaviour of the quadratic subfield units, see L. C. Washington, Introduction to Cyclotomic Fields (2nd ed., GTM 83), Section 5.5 (Leopoldt's conjecture; Theorem 5.29 and its proof for abelian fields) and the Kuroda class number formula context for biquadratic fields (Kuroda 1950; cf. Lemmermeyer, Kuroda's class number formula, Acta Arith. 66 (1994)).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_totallyReal_biquadratic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] [IsGalois ℚ K]
    (hK : Module.finrank ℚ K = 4) (hG : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
