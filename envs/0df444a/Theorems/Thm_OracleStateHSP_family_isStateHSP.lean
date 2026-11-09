-- Prove2me | Theorems.Thm_OracleStateHSP_family_isStateHSP
-- name    : OracleStateHSP.family_isStateHSP
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:32.117201+00:00
-- url     : https://prove2.me/theorems/cde9dbe1-8998-4689-ad3d-861e7a92d26f
-- title:
--   §4.3 items 1–2 after (55): $\{|\varphi^\varepsilon_f\rangle\}$ is a StateHSP family, $|H| = 2^{r+1}$, $|G/H| = 2^{m-1}$
-- statement:
--   Let $\varepsilon \in (0, 1]$, $r \ge 0$, and let $f : \mathbb Z_2^m \to \mathbb Z_2^m$ be a Simon function with nonzero period $s(f)$. Let $G = \mathbb Z_2^r \oplus \mathbb Z_2^m$ act by the shift representation $R$, and let $H = \mathbb Z_2^r \oplus \langle s(f) \rangle$. Then
--
--   1. $R(h)\,|\varphi^\varepsilon_f\rangle = |\varphi^\varepsilon_f\rangle$ for every $h \in H$;
--   2. for every $g \in G \setminus H$,
--   $$
--   \langle \varphi^\varepsilon_f | R(g) | \varphi^\varepsilon_f \rangle = (1-\varepsilon)\, \langle u_G | R(g) | u_G \rangle + \varepsilon\, \langle \varphi_f | R(g) | \varphi_f \rangle = 1 - \varepsilon ;
--   $$
--   3. $U_\varphi = O^\varepsilon_f W$ is a StateHSP instance (Definition 1.3) for $R$ with hidden subgroup $H$ and parameter $\varepsilon$;
--   4. $|H| = 2^{r+1}$ and $|G/H| = 2^{m-1}$.
--
--   These are the facts that make $\{|\varphi^\varepsilon_f\rangle\}_f$ a family of StateHSP instances with tunable parameter $\varepsilon$ and known $\log|G/H| = m - 1$.
--
--   **Formalization Note** The middle terms $\langle u_G|R(g)|u_G\rangle$ and $\langle\varphi_f|R(g)|\varphi_f\rangle$ are computed on the flagged vectors $|0\rangle|u_G\rangle$ and $|1\rangle|\varphi_f\rangle$, on which $R(g)$ acts as on $|u_G\rangle$ and $|\varphi_f\rangle$ (it is the identity on the flag).
--
--   Differences from the source:
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
--   - encoding: f ranges over Simon functions with nonzero period s(f) → x ranges over pairs (f, s) with f hiding s and s ≠ 0; reason: a nonzero period is unique, so the pairs are in bijection with the functions
--   - encoding: ⟨u_G|R(g)|u_G⟩ and ⟨φ_f|R(g)|φ_f⟩ → the same inner products on |0⟩|u_G⟩ and |1⟩|φ_f⟩; reason: R(g) is the identity on the flag, so the values coincide
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, items 1–2 after eq. (55), p.39; proof of Theorem 4.10, p.40 (|H| = 2^{r+1}, log|G/H| = m − 1); p.38 (|G/H̃| = 2^{m−1})

import Mathlib
import Definitions.Def_OracleStateHSP_IsStateHSPInstance
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_hiddenSubgroup
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_shiftRep
import Definitions.Def_OracleStateHSP_phiEps
import Definitions.Def_OracleStateHSP_fracU

namespace OracleStateHSP

open QAlgorithms

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.3, items 1–2 after eq. (55), p.39, and the proof of Theorem 4.10, p.40
("`|H| = 2^{r+1}` and `log |G/H| = m − 1`"): for `ε ∈ (0, 1]` and every Simon function `f` on
`Z_2^m` with nonzero period `s(f)`, with `G = Z_2^r ⊕ Z_2^m`, the shift representation `R` and
`H = Z_2^r ⊕ ⟨s(f)⟩`,

1. `R(h)|φ^ε_f⟩ = |φ^ε_f⟩` for every `h ∈ H`;
2. `⟨φ^ε_f|R(g)|φ^ε_f⟩ = (1 − ε) ⟨u_G|R(g)|u_G⟩ + ε ⟨φ_f|R(g)|φ_f⟩ = 1 − ε` for every
   `g ∈ G \ H`, where `⟨u_G|R(g)|u_G⟩` and `⟨φ_f|R(g)|φ_f⟩` are computed on the flagged vectors
   `|0⟩|u_G⟩` and `|1⟩|φ_f⟩` (on which `R(g)` acts as on `|u_G⟩`, `|φ_f⟩`);
3. `U_φ = O^ε_f W`, `R`, `H` form a StateHSP instance with parameter `ε` (Definition 1.3);
4. `|H| = 2^{r+1}` and `|G/H| = 2^{m−1}`.

**Formalization Note.** `Z_2^n` is `Z_2^r × Z_2^m` (`n = r + m`); the instance is the pair
`(f, s(f))`. -/
theorem family_isStateHSP (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ) (x : SimonInst m) :
    (∀ h ∈ hiddenSubgroup r x.period,
        act (shiftRep r m h) (phiEps ε r x.fn) = phiEps ε r x.fn) ∧
    (∀ g, g ∉ hiddenSubgroup r x.period →
        let u0 : EuclideanSpace ℂ (FlagQ r m) :=
          WithLp.toLp 2 fun p => if p.1 = 0 then uG r m p.2 else 0
        let f1 : EuclideanSpace ℂ (FlagQ r m) :=
          WithLp.toLp 2 fun p => if p.1 = 1 then phiF r x.fn p.2 else 0
        inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
            ((1 - ε : ℝ) : ℂ) * inner ℂ u0 (act (shiftRep r m g) u0) +
              (ε : ℂ) * inner ℂ f1 (act (shiftRep r m g) f1) ∧
          inner ℂ (phiEps ε r x.fn) (act (shiftRep r m g) (phiEps ε r x.fn)) =
            ((1 - ε : ℝ) : ℂ)) ∧
    IsStateHSPInstance (shiftRep r m) (flagZero r m) (fracU ε r x.fn)
      (hiddenSubgroup r x.period) ε ∧
    Nat.card (hiddenSubgroup r x.period) = 2 ^ (r + 1) ∧
    Nat.card ((K r × V m) ⧸ hiddenSubgroup r x.period) = 2 ^ (m - 1) := by sorry

end OracleStateHSP
