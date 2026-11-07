-- Prove2me | Theorems.Thm_ModFormPIR_theorem_7_1
-- name    : ModFormPIR.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:20.714196+00:00
-- url     : https://prove2.me/theorems/6766897c-be8b-4097-b135-4db177b18775
-- title:
--   Theorem 7.1, p.27 — a sparse expansion gives the correct, private scheme of Fig. 5
-- statement:
--   Let $s\ge2$, let $q\ge\max\{3,s\}$ be prime, and let $c$ be a $(k,s)$-sparse quadratic-phase delta expansion of order $q$ and dimension $d$ over a field with an element $\gamma$ of order $q$. Then the $s$-server scheme of Fig. 5 on databases of $q^d$ entries has:
--
--   1. correctness: the record (17) equals $\mathrm{DB}_i$, for all $\mathrm{DB}$, $i$, $r$;
--   2. information-theoretic security: under uniform $r$, $\mathrm{qu}_t=r-2t\,i$ is uniform whatever $i$;
--   3. each server stores $q^d$ entries, computed in $O(dq^d)$ field operations;
--   4. the user uploads $\lceil d\log_2q\rceil$ bits to each server;
--   5. each server reads at most $k$ entries, using $O(d)$ operations per entry to compute the point $\mathrm{qu}_t+w$.
--
--   This turns sparsity of an expansion into server work, and it is why the number of servers equals the size of $\mathcal A$.
--
--   **Formalization Note** A constant $C$ depending only on $q$ and $s$ bounds both operation counts, which count gates of a straight-line program over the field and over $\mathbb Z_q$.
--
--   Differences from the source:
--   - generalization: a field 𝔽_p → any field with an element γ of order q; reason: the proof never uses finiteness of the field; 𝔽_p is an instance
--   - reading: "there is an s-server PIR scheme" → the explicit scheme of Fig. 5; reason: the scheme the theorem’s proof constructs, which makes correctness and privacy statable
--   - reading: "O(dq^d) operations over 𝔽_p", "O(d) operations per element" → gates of a straight-line program over the field and over ℤ_q, at most C·d·q^d and C·d; reason: the source counts operations with no model; the constant may depend on q, as §7.2 says
--   - encoding: "⌈d log₂ q⌉ bits" → an injective encoding of ℤ_q^d into ⌈d log₂ q⌉ bits; reason: it is the query space that is uploaded
--   - encoding: integer d → 1 ≤ d; reason: §7.1 takes d ≥ 1
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 7.1, p.27 (PDF p.31), Fig. 5, p.27, §§7.1–7.2, pp.28–29

import Mathlib
import Definitions.Def_ModFormPIR_Expansion

open Matrix

set_option autoImplicit false

namespace ModFormPIR

/-- **Theorem 7.1**, p.27, with Fig. 5 and §7.2, pp.27–29. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
If `c` is a `(k, s)`-sparse quadratic-phase delta expansion of order `q` and dimension `d`, then the scheme of Fig. 5 on `q^d`
records is correct and private, with the stated efficiency.

**Formalization Note.** Over any field with an element `γ` of order `q`, which includes `𝔽_p`. The servers are the `s` elements
of `𝒜`, enlarged as in §7.1. The scheme is the explicit one of Fig. 5. "Operations over `𝔽_p`" are gates of a straight-line program over the
field; "`O(d)` operations per element" are gates over `ℤ_q` computing the point `qu_t + w`. `C` depends only on `q, s`. Privacy is
the law of `qu_t` under uniform `r`, which is uniform whatever the index. -/
theorem theorem_7_1 (q s : ℕ) [NeZero q] (hq : q.Prime) (hs : 2 ≤ s) (hsq : max 3 s ≤ q) :
    ∃ C : ℕ, ∀ (𝔽 : Type) [Field 𝔽] (d k : ℕ) (_ : 1 ≤ d) (γ : 𝔽) (_ : IsPrimitiveRoot γ q)
      (c : (Fin d → ZMod q) → ZMod q → 𝔽) (_ : IsDeltaExpansion γ c) (_ : IsSparse c k s),
      ∃ (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q)),
        HasSupport c (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q)) ∧ 𝒲.card ≤ k ∧ 𝒜.card = s ∧
        (∀ (DB : (Fin d → ZMod q) → 𝔽) (i r : Fin d → ZMod q),
          fig5Record γ c 𝒲 𝒜 DB i r = DB i) ∧
        (∀ (i : Fin d → ZMod q) (t : ZMod q),
          (PMF.uniformOfFintype (Fin d → ZMod q)).map (fun r => fig5Query r i t) =
            PMF.uniformOfFintype (Fin d → ZMod q)) ∧
        (∀ (r i : Fin d → ZMod q) (t : ZMod q),
          (𝒲.image fun w => fig5Query r i t + w).card ≤ k) ∧
        (∃ enc : (Fin d → ZMod q) → Fin ⌈(d : ℝ) * Real.logb 2 q⌉₊ → Bool,
          Function.Injective enc) ∧
        (∀ t ∈ 𝒜, ∃ (gs : List (Gate 𝔽 (Fin d → ZMod q))) (out : (Fin d → ZMod q) → ℕ),
          gs.length ≤ C * d * q ^ d ∧
          ComputesBy gs out fun DB x => fig5Table γ DB t x) ∧
        (∀ w ∈ 𝒲, ∃ (gs : List (Gate (ZMod q) (Fin d))) (out : Fin d → ℕ),
          gs.length ≤ C * d ∧ ComputesBy gs out fun u => u + w) := by sorry

end ModFormPIR
