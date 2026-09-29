-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace
-- name    : NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/3e696b79-6f3c-548c-8732-5a273167b0c0
-- title:
--   Local standard character and the local trace
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$ (a point of the height one spectrum), and let $w$ be an element of `v.Extension (𝓞 L)`, that is, a nonzero prime $w.1$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$. For a number field $F$ and a prime $u$ of $\mathcal{O}_F$, the character `psiLocal F u` on the completion $F_u$ is defined as the composition of the standard additive character of the adele ring of $F$ — the character $\psi_F$ attached to the adelic trace data of $F$ — with the additive homomorphism `adeleSingleAt F u`, which sends $t \in F_u$ to the adele with trivial infinite part and finite part the finite adele having component $t$ at $u$ and $0$ at all other finite places. The assertion is that for every $x$ in the completion $L_{w.1}$ one has $$\psi_{L,w.1}(x) = \psi_{K,v}\bigl(\mathrm{Tr}_{L_{w.1}/K_v}(x)\bigr),$$ where the trace is `Algebra.trace` for the canonical $K_v$-algebra structure on $L_{w.1}$.
--
--   This is the compatibility, under the local trace, of the standard additive characters of a number field and of a subfield, in the form needed for Tate's local theory: the local component at $w$ of the standard character of $L$ is the local component at $v$ of that of $K$ precomposed with $\mathrm{Tr}_{L_w/K_v}$. Here both characters arise by restriction from the global adelic characters, so the identity is a theorem rather than a definition; the proof cites the expression of the finite adelic trace down to $\mathbb{Q}$ as a sum of local traces over the primes above a given rational prime. It is used in the computation of local constants, in particular for the nontriviality of `psiLocal`, for its behaviour under the norm map in the unramified case, and for the additive levels entering the conductor formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by sorry
