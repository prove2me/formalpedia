-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_totallyReal_multiquadratic
-- name    : Leopoldt.leopoldt_totallyReal_multiquadratic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:14.338879+00:00
-- url     : https://prove2.me/theorems/a81a82c7-09f3-4144-9d58-9d05833bacc0
-- title:
--   Leopoldt's conjecture for totally real multiquadratic fields
-- statement:
--   Leopoldt's conjecture holds, at every prime $p$, for every totally real **multiquadratic** field. Precisely: let $\mathbb{K}$ be a totally real number field, Galois over $\mathbb{Q}$, such that every element of $G = \mathrm{Gal}(\mathbb{K}/\mathbb{Q})$ satisfies $\sigma^2 = 1$. Then
--
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E}) \;=\; 0 .$$
--
--   Here $E = \mathcal{O}_{\mathbb{K}}^\times$ and $\overline{E}$ is the $p$-adic closure of the diagonal image of $E$ in the semilocal units $U = \prod_{\mathfrak{P} \mid p} \mathcal{O}_{\mathfrak{P}}^\times$.
--
--   The hypothesis says $G \cong (\mathbb{Z}/2)^k$, i.e. $\mathbb{K} = \mathbb{Q}(\sqrt{a_1}, \dots, \sqrt{a_k})$ with all $a_i > 0$, of degree $2^k$ and unit rank $2^k - 1$. This generalises the real quadratic ($k = 1$) and real biquadratic ($k = 2$) cases. It is a special case of Brumer's theorem for abelian fields, but it admits an elementary proof: $\mathbb{K}$ has exactly $2^k - 1$ real quadratic subfields $k_\chi$ (one for each nontrivial character $\chi : G \to \{\pm 1\}$), a suitable power $\eta_\chi$ of the fundamental unit of $k_\chi$ satisfies $\sigma(\eta_\chi) = \eta_\chi^{\chi(\sigma)}$, and operators of the form $u \mapsto u\,\sigma(u)^{\pm 1}$ in $\mathbb{Z}[G]$ separate these eigen-units $p$-adically.
--
--   **Formalization note.** "Multiquadratic" is spelled as `IsGalois ℚ K` together with `∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1`; "totally real" as `IsTotallyReal K`. The degree is arbitrary (including $\mathbb{K} = \mathbb{Q}$), and no hypothesis on $p$ beyond primality is needed; in particular $p = 2$ is allowed.
-- source:
--   A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124 (Leopoldt's conjecture for abelian extensions of Q). For the elementary argument in the multiquadratic case (eigen-decomposition of the unit group under the characters of Gal(K/Q) = (Z/2)^k, with the units of the 2^k - 1 real quadratic subfields spanning a subgroup of finite index), see L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Section 5.5 (Leopoldt's conjecture, Theorem 5.29) and Section 8.1 (units of abelian fields: the character decomposition of the unit group); cf. H. Hasse, Über die Klassenzahl abelscher Zahlkörper (1952) for units of multiquadratic fields.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_totallyReal_multiquadratic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] [IsGalois ℚ K]
    (hG : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
