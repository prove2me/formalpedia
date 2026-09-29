-- Prove2me | Theorems.Thm_Leopoldt_exists_semilocalNorm
-- name    : Leopoldt.exists_semilocalNorm
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T03:01:14.885663+00:00
-- url     : https://prove2.me/theorems/5e6ea0d1-8122-48c2-85e8-bc410eeb968d
-- title:
--   Semilocal norm $N : U_p(\mathbb{K}) \to U_p(\mathbb{F})$ extending $N_{\mathbb{K}/\mathbb{F}}$ with $N\circ\varphi = (\cdot)^{[\mathbb{K}:\mathbb{F}]}$
-- statement:
--   Let $p$ be a prime and let $\mathbb{F} \subseteq \mathbb{K}$ be number fields, $n = [\mathbb{K} : \mathbb{F}]$. For a number field $\mathbb{L}$ write $U_p(\mathbb{L}) = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$ for the semilocal units at $p$ (product topology) and $\iota_{\mathbb{L}} : E(\mathbb{L}) = \mathcal{O}(\mathbb{L})^\times \to U_p(\mathbb{L})$ for the diagonal embedding of the global units, as in Section 1.1 of the source.
--
--   Then there are continuous group homomorphisms
--
--   $$\varphi : U_p(\mathbb{F}) \longrightarrow U_p(\mathbb{K}), \qquad N : U_p(\mathbb{K}) \longrightarrow U_p(\mathbb{F})$$
--
--   such that
--
--   1. $\varphi$ is injective and compatible with the inclusion of global units: $\varphi(\iota_{\mathbb{F}}(\varepsilon)) = \iota_{\mathbb{K}}(\varepsilon)$ for every $\varepsilon \in E(\mathbb{F})$;
--   2. $N$ extends the global norm: $N(\iota_{\mathbb{K}}(\varepsilon)) = \iota_{\mathbb{F}}\bigl(N_{\mathbb{K}/\mathbb{F}}(\varepsilon)\bigr)$ for every $\varepsilon \in E(\mathbb{K})$;
--   3. $N \circ \varphi$ is the $n$-th power map: $$N(\varphi(x)) = x^{[\mathbb{K}:\mathbb{F}]} \qquad \text{for all } x \in U_p(\mathbb{F}).$$
--
--   Concretely, $\varphi$ is the semilocal inclusion (on the factor at $\mathfrak{P} \mid p$ of $\mathbb{K}$ it is the continuous embedding $\mathbb{F}_\wp \hookrightarrow \mathbb{K}_\mathfrak{P}$ applied to the component at $\wp = \mathfrak{P} \cap \mathcal{O}(\mathbb{F})$), and $N$ is the semilocal norm, whose component at $\wp$ is
--   $$N(y)_\wp = \prod_{\mathfrak{P} \mid \wp} N_{\mathbb{K}_\mathfrak{P}/\mathbb{F}_\wp}(y_\mathfrak{P}).$$
--   Property 2 is the local–global norm identity $N_{\mathbb{K}/\mathbb{F}} = \prod_{\mathfrak{P}\mid\wp} N_{\mathbb{K}_\mathfrak{P}/\mathbb{F}_\wp}$ coming from $\mathbb{F}_\wp \otimes_{\mathbb{F}} \mathbb{K} \cong \prod_{\mathfrak{P} \mid \wp} \mathbb{K}_\mathfrak{P}$, and property 3 is the degree formula $\sum_{\mathfrak{P} \mid \wp} [\mathbb{K}_\mathfrak{P} : \mathbb{F}_\wp] = [\mathbb{K} : \mathbb{F}]$ (Neukirch, ANT II.8). This is the "norm" side of Remark 1.A of the source: together with $\varphi$ it lets one pass relations between $p$-adic closures of units up and down the extension, since $N \circ \varphi$ is multiplication by $[\mathbb{K}:\mathbb{F}]$ on the $\mathbb{Z}_p$-module $U_p(\mathbb{F})$.
--
--   **Formalization Note** The fields are related by an `Algebra F K` instance (finiteness of $\mathbb{K}/\mathbb{F}$ is automatic for number fields). `SemilocalUnits p L` and `diagonalUnits p L` are from the definition file. The global norm on units is `Units.map (RingOfIntegers.norm F)`, where `NumberField.RingOfIntegers.norm F : 𝓞 K →* 𝓞 F` is Mathlib's restriction of `Algebra.norm F` to rings of integers; the inclusion of units is `Units.map` of `algebraMap (𝓞 F) (𝓞 K)`. The two maps are bundled in one existential so that property 3 refers to the same $\varphi$ as property 1.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4), Section 1.1 (definition of U and iota, p. 3) and Section 1.3, Remark 1 part A (p. 5), which uses the norm N_{K/K_1} on units together with the embedding E(K_1) -> E(K). Local-global facts: J. Neukirch, Algebraic Number Theory, Ch. II, Prop. 8.3 (K tensor_F F_v = prod_{w|v} K_w) and Cor. 8.4 (N_{K/F}(a) = prod_{w|v} N_{K_w/F_v}(a), sum_{w|v} [K_w:F_v] = [K:F]).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem exists_semilocalNorm (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] :
    ∃ (φ : SemilocalUnits p F →* SemilocalUnits p K) (N : SemilocalUnits p K →* SemilocalUnits p F),
      Continuous φ ∧ Function.Injective φ ∧
      (∀ ε : (𝓞 F)ˣ, φ (diagonalUnits p F ε) =
        diagonalUnits p K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom ε)) ∧
      Continuous N ∧
      (∀ ε : (𝓞 K)ˣ, N (diagonalUnits p K ε) =
        diagonalUnits p F (Units.map (RingOfIntegers.norm F) ε)) ∧
      ∀ x, N (φ x) = x ^ Module.finrank F K := by sorry
end Leopoldt
